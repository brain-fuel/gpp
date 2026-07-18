package gen

import (
	"go/ast"
	"go/token"
	"strings"

	"goforge.dev/gpp/internal/diag"
	"goforge.dev/gpp/internal/naming"
	"goforge.dev/gpp/internal/registry"
	"goforge.dev/gpp/internal/syntax"
)

// planClasses validates class and instance declarations before lowering
// and builds the registry models resolution consumes (PkgPath left
// provisional; buildRegistry stamps it). Pass 1 needs no cross-file class
// knowledge — witness fields and methods render from verbatim source
// slices; embed flattening, default filling, and dictionary wiring happen
// at resolve.
func planClasses(idx *pkgIndex, tbl *naming.Table) ([]*registry.Class, []*registry.Instance, []diag.Diagnostic) {
	var classModels []*registry.Class
	var instModels []*registry.Instance
	var diags []diag.Diagnostic
	errAt := func(pos token.Pos, format string, args ...any) {
		diags = append(diags, diag.At(idx.fset.Position(pos), format, args...))
	}

	for _, f := range idx.files {
		if f.gpp == nil {
			continue
		}
		for _, c := range f.gpp.Classes {
			name := c.Spec.Name.Name
			if c.Gen.Lparen.IsValid() || len(c.Gen.Specs) > 1 {
				errAt(c.Spec.Pos(), "declare each class in its own type declaration (class %s is inside a grouped type block)", name)
				continue
			}
			tp := c.Spec.TypeParams
			nTParams := 0
			if tp != nil {
				for _, field := range tp.List {
					nTParams += len(field.Names)
				}
			}
			if nTParams != 1 {
				errAt(c.Spec.Pos(), "a class must have exactly one type parameter (v0.5.0); %s has %d", name, nTParams)
				continue
			}
			if len(c.Members) == 0 {
				errAt(c.ClassPos, "class %s must declare at least one member", name)
				continue
			}
			seenOps := map[string]token.Pos{}
			seenLaws := map[string]token.Pos{}
			for _, m := range c.Members {
				if m.Name == nil {
					continue
				}
				n := m.Name.Name
				if m.LawPos.IsValid() {
					if _, dup := seenLaws[n]; dup {
						errAt(m.Name.Pos(), "class %s declares law %s twice", name, n)
					}
					seenLaws[n] = m.Name.Pos()
				} else {
					if _, dup := seenOps[n]; dup {
						errAt(m.Name.Pos(), "class %s declares operation %s twice", name, n)
					}
					seenOps[n] = m.Name.Pos()
				}
			}
			// Generated method names must not collide with operations.
			for law := range seenLaws {
				if pos, hit := seenOps["Law"+law]; hit {
					errAt(pos, "operation Law%s collides with the generated method for law %s; rename one", law, law)
				}
			}
			for op := range seenOps {
				if pos, hit := seenOps["Default"+op]; hit && "Default"+op != op {
					errAt(pos, "operation Default%s collides with the generated method for %s's default; rename one", op, op)
				}
			}

			model := &registry.Class{Name: name}
			if tp != nil && len(tp.List) > 0 && len(tp.List[0].Names) > 0 {
				model.TParam = tp.List[0].Names[0].Name
			}
			for _, m := range c.Members {
				switch {
				case m.Embed != nil:
					if ref, ok := embedClassRef(f.gpp, m.Embed); ok {
						model.Embeds = append(model.Embeds, ref)
					} else {
						errAt(m.Embed.Pos(), "class %s embeds something that is not a class reference", name)
					}
				case m.LawPos.IsValid():
					params := string(f.gpp.Src[f.gpp.Offset(m.Params.Opening)+1 : f.gpp.Offset(m.Params.Closing)])
					model.Laws = append(model.Laws, registry.ClassLaw{Name: m.Name.Name, Params: params})
				default:
					model.Ops = append(model.Ops, m.Name.Name)
					if m.Body != nil {
						model.Defaults = append(model.Defaults, m.Name.Name)
					}
				}
			}
			classModels = append(classModels, model)
		}

		for _, d := range f.gpp.Instances {
			// Instance names hide behind BadDecls, so the authored-name
			// sweep misses them; record them here.
			tbl.AddAuthored(d.Name.Name, idx.fset.Position(d.Name.Pos()).String())
			seen := map[string]bool{}
			for _, m := range d.Members {
				if seen[m.Name.Name] {
					errAt(m.Name.Pos(), "instance %s implements %s twice", d.Name.Name, m.Name.Name)
				}
				seen[m.Name.Name] = true
			}

			model := &registry.Instance{Name: d.Name.Name, Generic: d.TParams != nil}
			if d.TParams != nil {
				model.TParamsText = string(f.gpp.Src[f.gpp.Offset(d.TParams.Opening)+1 : f.gpp.Offset(d.TParams.Closing)])
			}
			ref, args, ok := instanceClassParts(f.gpp, d.Class)
			if !ok {
				errAt(d.Class.Pos(), "instance %s does not name a class", d.Name.Name)
				continue
			}
			model.Class, model.ClassArgs = ref, args
			model.LawsMode = lawsDirective(d.Doc)
			instModels = append(instModels, model)
		}
	}
	return classModels, instModels, diags
}

// embedClassRef interprets an embed expression as a class reference
// (local: PkgPath ""; imported: resolved through the file's imports).
func embedClassRef(f *syntax.File, embed ast.Expr) (registry.ClassRef, bool) {
	root := embed
	for {
		switch t := root.(type) {
		case *ast.IndexExpr:
			root = t.X
			continue
		case *ast.IndexListExpr:
			root = t.X
			continue
		}
		break
	}
	switch t := root.(type) {
	case *ast.Ident:
		return registry.ClassRef{Name: t.Name}, true
	case *ast.SelectorExpr:
		alias, _ := t.X.(*ast.Ident)
		if alias == nil {
			return registry.ClassRef{}, false
		}
		if path, ok := importPathIn(f, alias.Name); ok {
			return registry.ClassRef{PkgPath: path, Name: t.Sel.Name}, true
		}
	}
	return registry.ClassRef{}, false
}

// instanceClassParts splits an instance head into its class ref and the
// type-argument text.
func instanceClassParts(f *syntax.File, class ast.Expr) (registry.ClassRef, string, bool) {
	var argsText string
	root := class
	switch t := root.(type) {
	case *ast.IndexExpr:
		argsText = string(f.Src[f.Offset(t.Index.Pos()):f.Offset(t.Index.End())])
		root = t.X
	case *ast.IndexListExpr:
		if len(t.Indices) > 0 {
			argsText = string(f.Src[f.Offset(t.Indices[0].Pos()):f.Offset(t.Indices[len(t.Indices)-1].End())])
		}
		root = t.X
	default:
		return registry.ClassRef{}, "", false
	}
	switch t := root.(type) {
	case *ast.Ident:
		return registry.ClassRef{Name: t.Name}, argsText, true
	case *ast.SelectorExpr:
		alias, _ := t.X.(*ast.Ident)
		if alias == nil {
			return registry.ClassRef{}, "", false
		}
		if path, ok := importPathIn(f, alias.Name); ok {
			return registry.ClassRef{PkgPath: path, Name: t.Sel.Name}, argsText, true
		}
	}
	return registry.ClassRef{}, "", false
}

// importPathIn resolves an import alias in one file.
func importPathIn(f *syntax.File, alias string) (string, bool) {
	for _, imp := range f.AST.Imports {
		path := strings.Trim(imp.Path.Value, "\"")
		name := ""
		if imp.Name != nil {
			name = imp.Name.Name
		} else if i := strings.LastIndex(path, "/"); i >= 0 {
			name = path[i+1:]
		} else {
			name = path
		}
		if name == alias {
			return path, true
		}
	}
	return "", false
}

// lawsDirective extracts the raw //gpp:laws value from an instance's doc.
func lawsDirective(doc *ast.CommentGroup) string {
	if doc == nil {
		return ""
	}
	for _, c := range doc.List {
		if rest, ok := strings.CutPrefix(strings.TrimSpace(c.Text), "//gpp:laws"); ok {
			return strings.TrimSpace(rest)
		}
	}
	return ""
}
