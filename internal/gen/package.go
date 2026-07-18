package gen

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"reflect"

	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/syntax"
)

// sourceFile is one file participating in a package: authored .go or .gpp.
type sourceFile struct {
	path string // absolute
	base string // basename
	src  []byte
	ast  *ast.File
	gpp  *syntax.File // non-nil for .gpp files
}

// pkgIndex indexes one directory's files for name and type lookups.
type pkgIndex struct {
	fset  *token.FileSet
	files []*sourceFile
}

// typeSpec finds the declaration of a named type anywhere in the package.
func (p *pkgIndex) typeSpec(name string) (*ast.TypeSpec, *sourceFile) {
	for _, f := range p.files {
		for _, decl := range f.ast.Decls {
			gd, ok := decl.(*ast.GenDecl)
			if !ok {
				continue
			}
			for _, spec := range gd.Specs {
				if ts, ok := spec.(*ast.TypeSpec); ok && ts.Name.Name == name {
					return ts, f
				}
			}
		}
	}
	return nil, nil
}

// receiverTParams resolves the receiver's type parameters to (name,
// constraint) pairs, with constraints taken from the receiver type's
// declaration and rewritten into the names used on the receiver.
func receiverTParams(idx *pkgIndex, gm *syntax.GenericMethod) ([]lower.TParam, error) {
	if len(gm.RecvTParams) == 0 {
		return nil, nil
	}
	ts, declFile := idx.typeSpec(gm.RecvTypeName)
	if ts == nil {
		return nil, fmt.Errorf("cannot find the declaration of receiver type %s in this package", gm.RecvTypeName)
	}
	if ts.TypeParams == nil {
		return nil, fmt.Errorf("receiver type %s is not generic but the receiver lists type parameters", gm.RecvTypeName)
	}
	var declNames []string
	var constraints []ast.Expr
	for _, field := range ts.TypeParams.List {
		for _, n := range field.Names {
			declNames = append(declNames, n.Name)
			constraints = append(constraints, field.Type)
		}
	}
	if len(declNames) != len(gm.RecvTParams) {
		return nil, fmt.Errorf("receiver lists %d type parameters but %s declares %d",
			len(gm.RecvTParams), gm.RecvTypeName, len(declNames))
	}
	rename := map[string]string{}
	for i, dn := range declNames {
		rn := gm.RecvTParams[i]
		if rn == "_" {
			return nil, fmt.Errorf("receiver type parameters of a generic method must be named, not _")
		}
		rename[dn] = rn
	}
	out := make([]lower.TParam, len(declNames))
	for i := range declNames {
		text, err := renderConstraint(idx.fset, declFile, constraints[i], rename)
		if err != nil {
			return nil, err
		}
		out[i] = lower.TParam{Name: gm.RecvTParams[i], Constraint: text}
	}
	return out, nil
}

// renderConstraint renders a constraint expression, renaming type parameter
// references from the type declaration's names to the receiver's names.
// When no renaming applies, the original source text is used verbatim.
func renderConstraint(fset *token.FileSet, declFile *sourceFile, expr ast.Expr, rename map[string]string) (string, error) {
	tf := fset.File(declFile.ast.Pos())
	text := string(declFile.src[tf.Offset(expr.Pos()):tf.Offset(expr.End())])

	needsRename := false
	for from, to := range rename {
		if from != to && identReferenced(expr, from) {
			needsRename = true
			break
		}
	}
	if !needsRename {
		return text, nil
	}

	parsed, err := parser.ParseExpr(text)
	if err != nil {
		return "", fmt.Errorf("internal error: re-parsing constraint %q: %w", text, err)
	}
	renameTypeRefs(parsed, rename)
	var buf bytes.Buffer
	if err := printer.Fprint(&buf, token.NewFileSet(), parsed); err != nil {
		return "", err
	}
	return buf.String(), nil
}

func identReferenced(root ast.Node, name string) bool {
	found := false
	visitTypeRefIdents(root, func(id *ast.Ident) {
		if id.Name == name {
			found = true
		}
	})
	return found
}

func renameTypeRefs(root ast.Node, rename map[string]string) {
	visitTypeRefIdents(root, func(id *ast.Ident) {
		if to, ok := rename[id.Name]; ok {
			id.Name = to
		}
	})
}

// substituteTypeText replaces type-parameter references in a type
// expression's source text with ground type texts (GADT variants fix some
// enum type parameters, and their field types must follow). AST-driven:
// selector members and field names that merely coincide lexically are
// never touched.
func substituteTypeText(text string, subst map[string]string) (string, error) {
	if len(subst) == 0 {
		return text, nil
	}
	expr, err := parser.ParseExpr(text)
	if err != nil {
		return "", fmt.Errorf("internal error: re-parsing type %q: %w", text, err)
	}
	replacements := map[string]ast.Expr{}
	for from, to := range subst {
		rexpr, rerr := parser.ParseExpr(to)
		if rerr != nil {
			return "", fmt.Errorf("internal error: re-parsing substitution %q: %w", to, rerr)
		}
		replacements[from] = rexpr
	}
	// Root may itself be a substituted ident.
	if id, ok := expr.(*ast.Ident); ok {
		if _, hit := replacements[id.Name]; hit {
			return subst[id.Name], nil
		}
	}
	skip := map[*ast.Ident]bool{}
	ast.Inspect(expr, func(n ast.Node) bool {
		switch node := n.(type) {
		case *ast.SelectorExpr:
			skip[node.Sel] = true
		case *ast.Field:
			for _, name := range node.Names {
				skip[name] = true
			}
		}
		return true
	})
	replaceChildIdents(expr, replacements, skip)
	var buf bytes.Buffer
	if err := printer.Fprint(&buf, token.NewFileSet(), expr); err != nil {
		return "", err
	}
	return buf.String(), nil
}

// replaceChildIdents rewrites, via reflection, every child field of type
// ast.Expr (or []ast.Expr) holding a matching *ast.Ident.
func replaceChildIdents(root ast.Node, repl map[string]ast.Expr, skip map[*ast.Ident]bool) {
	exprType := reflect.TypeOf((*ast.Expr)(nil)).Elem()
	swap := func(v reflect.Value) {
		if !v.CanSet() || v.IsNil() {
			return
		}
		if id, ok := v.Interface().(*ast.Ident); ok && !skip[id] {
			if r, hit := repl[id.Name]; hit {
				v.Set(reflect.ValueOf(r))
			}
		}
	}
	ast.Inspect(root, func(n ast.Node) bool {
		if n == nil {
			return false
		}
		rv := reflect.ValueOf(n)
		if rv.Kind() != reflect.Pointer || rv.IsNil() {
			return true
		}
		rv = rv.Elem()
		if rv.Kind() != reflect.Struct {
			return true
		}
		for i := 0; i < rv.NumField(); i++ {
			fv := rv.Field(i)
			switch {
			case fv.Type() == exprType:
				swap(fv)
			case fv.Kind() == reflect.Slice && fv.Type().Elem() == exprType:
				for j := 0; j < fv.Len(); j++ {
					swap(fv.Index(j))
				}
			}
		}
		return true
	})
}

// visitTypeRefIdents visits identifiers that are type references, skipping
// selector members (x.Sel), interface method names, and struct field names,
// which merely coincide lexically.
func visitTypeRefIdents(root ast.Node, visit func(*ast.Ident)) {
	skip := map[*ast.Ident]bool{}
	ast.Inspect(root, func(n ast.Node) bool {
		switch node := n.(type) {
		case *ast.SelectorExpr:
			skip[node.Sel] = true
		case *ast.Field:
			for _, name := range node.Names {
				skip[name] = true
			}
		}
		return true
	})
	ast.Inspect(root, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok && !skip[id] {
			visit(id)
		}
		return true
	})
}
