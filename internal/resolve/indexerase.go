package resolve

import (
	"go/ast"

	"goforge.dev/gpp/internal/lower"
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
