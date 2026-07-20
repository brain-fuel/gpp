package resolve

import (
	"go/ast"
	"go/types"
	"strconv"
	"strings"

	"goforge.dev/goplus/internal/lower"
)

// Uniform segment carriers (v0.4.0 Engine A). Pass 1 lowers every
// direct-callee pipe segment to `__gp_seg<k>(head, callee, fixed…)` and
// every dot segment's receiver to `__gp_dot(head)`, so resolution sees
// the flowing type at every stage. A non-Result head collapses to the
// exact v0.3 rendering; a Result head lifts onto the railway (phase 6).

// segCandidate collapses one __gp_seg<k> carrier.
func (r *fileResolver) segCandidate(call *ast.CallExpr) {
	fn, ok := call.Fun.(*ast.Ident)
	if !ok || !strings.HasPrefix(fn.Name, lower.SegCarrierPrefix) {
		return
	}
	insertAt, err := strconv.Atoi(strings.TrimPrefix(fn.Name, lower.SegCarrierPrefix))
	if err != nil || len(call.Args) < 2 {
		return
	}
	info := r.pkg.TypesInfo
	head := call.Args[0]
	tv, typed := info.Types[head]
	if !typed || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
		if r.report {
			r.errorf(call.Pos(), "cannot resolve this pipeline segment: the type of the piped value is unknown")
		}
		return
	}

	if T, E, isRes := r.isResult(tv.Type); isRes {
		if r.railwaySeg(call, insertAt, T, E) {
			return
		}
		// A stage that accepts the Result itself (or a non-function
		// callee) collapses to the direct call.
	}

	// Non-Result head: direct v0.3-shaped call.
	headText := r.text(head.Pos(), head.End())
	calleeText := r.text(call.Args[1].Pos(), call.Args[1].End())
	var finalArgs []string
	for i, a := range call.Args[2:] {
		text := r.text(a.Pos(), a.End())
		if i == len(call.Args[2:])-1 && call.Ellipsis.IsValid() {
			text += "..."
		}
		finalArgs = append(finalArgs, text)
	}
	if insertAt > len(finalArgs) {
		insertAt = len(finalArgs)
	}
	finalArgs = append(finalArgs[:insertAt], append([]string{headText}, finalArgs[insertAt:]...)...)
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(call.Pos()),
		End:   r.off(call.End()),
		New:   calleeText + "(" + strings.Join(finalArgs, ", ") + ")",
	})
}

// dotCandidate collapses one __gp_dot(head) marker.
func (r *fileResolver) dotCandidate(call *ast.CallExpr) {
	fn, ok := call.Fun.(*ast.Ident)
	if !ok || fn.Name != lower.DotCarrier || len(call.Args) != 1 {
		return
	}
	info := r.pkg.TypesInfo
	head := call.Args[0]
	tv, typed := info.Types[head]
	if !typed || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
		if r.report {
			r.errorf(call.Pos(), "cannot resolve this pipeline segment: the type of the piped value is unknown")
		}
		return
	}
	headText := r.text(head.Pos(), head.End())
	if needsParen(head) {
		headText = "(" + headText + ")"
	}
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(call.Pos()),
		End:   r.off(call.End()),
		New:   headText,
	})
}

// isResult reports whether t is a std/result Result instance. Railway
// support lands in phase 6; until then this recognizes the type so the
// direct path can stay honest.
func (r *fileResolver) isResult(t types.Type) (T, E types.Type, ok bool) {
	named, _ := asNamed(t)
	if named == nil || named.Obj().Pkg() == nil {
		return nil, nil, false
	}
	if named.Obj().Pkg().Path() != resultPkgPath || named.Obj().Name() != resultTypeName {
		return nil, nil, false
	}
	ta := named.TypeArgs()
	if ta == nil || ta.Len() != 2 {
		return nil, nil, false
	}
	return ta.At(0), ta.At(1), true
}

const (
	resultPkgPath  = "goforge.dev/goplus/std/result"
	resultTypeName = "Result"
)
