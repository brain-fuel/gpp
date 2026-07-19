package resolve

import (
	"go/ast"

	"goforge.dev/gpp/internal/lower"
)

// Dependent call sites (v0.7.0). The surface passes every argument —
// erased ones included (`Head(2, v)`); the signature dropped its
// 0-quantity parameters in pass 1, so the call drops the matching
// arguments here. Idempotent by arity: a call already at the erased
// arity is left alone. Erased arguments must be index expressions
// (pure); anything effectful is an error — its evaluation would vanish.

// depCallCandidate drops erased arguments from one call.
func (r *fileResolver) depCallCandidate(call *ast.CallExpr) {
	fnIdent, _, pkgPath := calleeIdent(r, call.Fun)
	if fnIdent == nil {
		return
	}
	d, ok := r.reg.LookupDepFn(pkgPath, fnIdent.Name)
	if !ok || len(d.Dropped) == 0 {
		return
	}
	if len(call.Args) != len(d.Params) {
		return // already erased (or an arity error for the backstop)
	}
	dropped := map[int]bool{}
	for _, i := range d.Dropped {
		dropped[i] = true
	}
	for i, a := range call.Args {
		if !dropped[i] {
			continue
		}
		if !pureIndexArg(a) {
			if r.report {
				r.errorf(a.Pos(), "the argument for erased parameter %s of %s must be an index expression (it is erased at runtime)",
					d.Params[i].Name, d.Name)
			}
			return
		}
	}
	for i, a := range call.Args {
		if !dropped[i] {
			continue
		}
		if i+1 < len(call.Args) {
			r.edits = append(r.edits, lower.Edit{Start: r.off(a.Pos()), End: r.off(call.Args[i+1].Pos()), New: ""})
		} else if i > 0 {
			r.edits = append(r.edits, lower.Edit{Start: r.off(call.Args[i-1].End()), End: r.off(a.End()), New: ""})
		} else {
			r.edits = append(r.edits, lower.Edit{Start: r.off(a.Pos()), End: r.off(a.End()), New: ""})
		}
	}
}

// pureIndexArg reports whether an expression is a pure index term:
// identifiers, literals, arithmetic, parens, and calls to totals
// (validated as total elsewhere; effectful calls are not total).
func pureIndexArg(e ast.Expr) bool {
	switch x := e.(type) {
	case *ast.Ident, *ast.BasicLit:
		return true
	case *ast.ParenExpr:
		return pureIndexArg(x.X)
	case *ast.BinaryExpr:
		return pureIndexArg(x.X) && pureIndexArg(x.Y)
	case *ast.SelectorExpr:
		return true
	case *ast.CallExpr:
		for _, a := range x.Args {
			if !pureIndexArg(a) {
				return false
			}
		}
		return pureIndexArg(x.Fun)
	}
	return false
}
