package resolve

import (
	"go/ast"
	"go/types"

	"goforge.dev/goplus/internal/lower"
	"goforge.dev/goplus/internal/registry"
)

// Bare operation names (v0.5.0). Inside constrained functions, law and
// default bodies, and instance constructors, class operations are in
// scope as bare names: `Combine(acc, x)` rewrites to `monoid.Combine(acc,
// x)` / `m.Combine(…)` / `w.Combine(…)`. A bare name that ALSO resolves
// in ordinary scope is a hard error demanding qualification. Receiver
// sugar `a.Combine(b)` applies when a's type is a constrained type
// parameter.

// opCallCandidate rewrites one bare-op call.
func (r *fileResolver) opCallCandidate(call *ast.CallExpr) {
	id, ok := call.Fun.(*ast.Ident)
	if !ok {
		return
	}
	info := r.pkg.TypesInfo
	ctx := r.enclosingWitnessContext(call)
	if ctx == nil {
		return
	}
	providers := r.opProviders(ctx, id.Name)
	if len(providers) == 0 {
		return
	}
	if info.Uses[id] != nil || info.Defs[id] != nil {
		// The name resolves in ordinary scope AND is a class operation.
		r.errorf(id.Pos(), "%s is both an operation of %s and a name in scope; write %s.%s for the operation or qualify the other use",
			id.Name, providers[0].class.Name, providers[0].expr, id.Name)
		return
	}
	if len(providers) > 1 {
		r.errorf(id.Pos(), "%s is provided by both %s (as %s) and %s (as %s); qualify the call",
			id.Name, providers[0].class.Name, providers[0].expr, providers[1].class.Name, providers[1].expr)
		return
	}
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(id.Pos()),
		End:   r.off(id.Pos()),
		New:   providers[0].expr + ".",
	})
}

// opProviders lists the in-scope witnesses whose class closure has an op.
func (r *fileResolver) opProviders(ctx *witnessContext, op string) []witnessDict {
	var out []witnessDict
	for _, d := range ctx.dicts {
		if _, has := r.reg.AllOps(d.class)[op]; has {
			out = append(out, d)
		}
	}
	return out
}

// opSugarCandidate rewrites `a.Combine(b)` where a's type is a
// constrained type parameter: the receiver becomes the first argument of
// the dictionary's operation.
func (r *fileResolver) opSugarCandidate(call *ast.CallExpr) {
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		return
	}
	info := r.pkg.TypesInfo
	tv, typed := info.Types[sel.X]
	if !typed || tv.Type == nil {
		return
	}
	tp, isTP := types.Unalias(tv.Type).(*types.TypeParam)
	if !isTP {
		return
	}
	ctx := r.enclosingWitnessContext(call)
	if ctx == nil {
		return
	}
	var match *witnessDict
	for i, d := range ctx.dicts {
		if d.tparam != tp.Obj().Name() {
			continue
		}
		if _, has := r.reg.AllOps(d.class)[sel.Sel.Name]; has {
			if match != nil {
				r.errorf(sel.Sel.Pos(), "%s is provided by both %s and %s; call through the witness instead",
					sel.Sel.Name, match.class.Name, d.class.Name)
				return
			}
			match = &ctx.dicts[i]
		}
	}
	if match == nil {
		return
	}
	recvText := r.text(sel.X.Pos(), sel.X.End())
	if needsParen(sel.X) {
		recvText = "(" + recvText + ")"
	}
	insertion := match.expr + "." + sel.Sel.Name + "(" + recvText
	if len(call.Args) > 0 {
		insertion += ", " + r.text(call.Args[0].Pos(), argEnd(call))
	}
	insertion += ")"
	r.edits = append(r.edits, lower.Edit{Start: r.off(call.Pos()), End: r.off(call.End()), New: insertion})
}

// opPipeRewrite gives pipe carriers access to bare ops: called from
// pipeCandidate when a bare segment name resolves to nothing else.
// Returns the witness expression when exactly one in-scope dictionary
// provides the op.
func (r *fileResolver) opPipeRewrite(call *ast.CallExpr, name string) (string, bool) {
	ctx := r.enclosingWitnessContext(call)
	if ctx == nil {
		return "", false
	}
	providers := r.opProviders(ctx, name)
	if len(providers) != 1 {
		return "", false
	}
	return providers[0].expr, true
}

var _ = registry.ClassRef{} // keep the import stable while candidates evolve
