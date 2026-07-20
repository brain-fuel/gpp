package resolve

import (
	"go/ast"
	"go/token"
	"strings"

	"goforge.dev/goplus/internal/lower"
)

// Cross-package index erasure (v0.7.0). Pass 1 erases index arguments
// from instantiations of SAME-package indexed enums; instantiations of
// imported ones (`vec.Vec[int, 2]`) survive into the generated text
// until the registry — which knows every reachable enum's index
// binders — identifies them here. Same-package uses arrive already
// erased (argument count mismatch) and are skipped.

// indexEraseCandidate drops index arguments from one instantiation.
func (r *fileResolver) indexEraseCandidate(base ast.Expr, args []ast.Expr, lbrack, rbrack int) {
	var pkgPath, name string
	switch b := base.(type) {
	case *ast.Ident:
		pkgPath, name = r.pkg.PkgPath, b.Name
	case *ast.SelectorExpr:
		alias, ok := b.X.(*ast.Ident)
		if !ok {
			return
		}
		path, found := fileImportPath(r.file, alias.Name)
		if !found {
			return
		}
		pkgPath, name = path, b.Sel.Name
	default:
		return
	}
	e, ok := r.reg.LookupEnum(pkgPath, name)
	if !ok || len(e.Indices) == 0 {
		return
	}
	arity := len(e.TParams) + len(e.Indices)
	if len(args) != arity {
		return
	}
	idxPos := map[int]bool{}
	for _, ib := range e.Indices {
		idxPos[ib.Pos] = true
	}
	// When the instantiation is a parameter type of an enclosing func,
	// record its index terms so match filtering can use them (the
	// generated text is about to lose them).
	if fn, param, isParam := r.enclosingParam(base); isParam {
		var terms []string
		for i, a := range args {
			if idxPos[i] {
				terms = append(terms, string(r.src[r.off(a.Pos()):r.off(a.End())]))
			}
		}
		r.reg.AddParamIndex(r.pkg.PkgPath, fn, param, name, terms)
	}

	kept := 0
	for i := range args {
		if !idxPos[i] {
			kept++
		}
	}
	if kept == 0 {
		r.edits = append(r.edits, lower.Edit{Start: lbrack, End: rbrack + 1, New: ""})
		return
	}
	for i, a := range args {
		if !idxPos[i] {
			continue
		}
		if i+1 < len(args) {
			r.edits = append(r.edits, lower.Edit{Start: r.off(a.Pos()), End: r.off(args[i+1].Pos()), New: ""})
		} else {
			r.edits = append(r.edits, lower.Edit{Start: r.off(args[i-1].End()), End: r.off(a.End()), New: ""})
		}
	}
}

// enclosingParam locates the func parameter whose type contains node.
func (r *fileResolver) enclosingParam(node ast.Expr) (fn, param string, ok bool) {
	for _, decl := range r.file.Decls {
		fd, isFn := decl.(*ast.FuncDecl)
		if !isFn || fd.Type.Params == nil {
			continue
		}
		if node.Pos() < fd.Type.Params.Pos() || node.Pos() >= fd.Type.Params.End() {
			continue
		}
		for _, fld := range fd.Type.Params.List {
			if node.Pos() >= fld.Type.Pos() && node.Pos() < fld.Type.End() && len(fld.Names) == 1 {
				return fd.Name.Name, fld.Names[0].Name, true
			}
		}
	}
	return "", "", false
}

// blankUnusedImports converts imports with no remaining references into
// blank imports: erased index vocabulary must not fail the backstop,
// and the import line must SURVIVE (markers resolve qualified sorts
// through it — reconstruction treats `_ "path"` as aliasable by the
// path's last segment).
func blankUnusedImports(file *ast.File, fset *token.FileSet, src []byte) []lower.Edit {
	tokFile := fset.File(file.Pos())
	used := map[string]bool{}
	ast.Inspect(file, func(n ast.Node) bool {
		if _, isImport := n.(*ast.ImportSpec); isImport {
			return false
		}
		if sel, ok := n.(*ast.SelectorExpr); ok {
			if id, isID := sel.X.(*ast.Ident); isID {
				used[id.Name] = true
			}
		}
		return true
	})
	var edits []lower.Edit
	for _, imp := range file.Imports {
		if imp.Name != nil {
			continue // aliased (incl. already-blank): leave alone
		}
		path := strings.Trim(imp.Path.Value, `"`)
		alias := path[strings.LastIndex(path, "/")+1:]
		if used[alias] {
			continue
		}
		at := tokFile.Offset(imp.Path.Pos())
		edits = append(edits, lower.Edit{Start: at, End: at, New: "_ "})
	}
	return edits
}
