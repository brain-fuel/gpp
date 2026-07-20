package resolve

import (
	"fmt"
	"go/ast"
	"go/types"
	"strings"

	"goforge.dev/goplus/internal/lower"
)

// Railway pipes (v0.4.0). When the flowing value of a pipeline is a
// Result[T, E], stages lift by shape — first match wins:
//
//  1. dot segments receive the RAW Result (members like .UnwrapOr)
//  2. a stage accepting the Result directly → direct call
//  3. T → Result[U, E]  → Bind   (the error types must match)
//  4. T → (U, error)    → Bind + Of adapter (E must be error)
//  5. T → U             → Map
//  6. T → ()            → Tee    (runs on Ok only; skipped on Err)
//  7. other shapes      → hard error
//
// Emission is std/result combinator calls; stage extra arguments close
// over in a function literal, so they evaluate on the Ok path only.

// railwaySeg lifts a __gp_seg<k> carrier whose head is Result[T, E].
// It reports whether it handled the carrier (edit, diagnostic, or wait);
// false falls through to the direct v0.3 collapse.
func (r *fileResolver) railwaySeg(call *ast.CallExpr, insertAt int, T, E types.Type) bool {
	info := r.pkg.TypesInfo
	callee := call.Args[1]
	ctv, typed := info.Types[callee]
	if !typed || ctv.Type == nil || ctv.Type == types.Typ[types.Invalid] {
		if r.report {
			r.errorf(call.Pos(), "cannot resolve this pipeline segment: the type of the stage is unknown")
		}
		return true // wait
	}
	sig, isSig := types.Unalias(ctv.Type).(*types.Signature)
	if !isSig {
		return false // conversion or other non-function callee: direct
	}
	var fixed []string
	for i, a := range call.Args[2:] {
		text := r.text(a.Pos(), a.End())
		if i == len(call.Args[2:])-1 && call.Ellipsis.IsValid() {
			text += "..."
		}
		fixed = append(fixed, text)
	}
	calleeText := r.text(callee.Pos(), callee.End())
	return r.railwayLift(call, call.Args[0], T, E, calleeText, fixed, insertAt, sig)
}

// railwayBare lifts a __gp_bare_ carrier (function reading) whose head
// is Result[T, E].
func (r *fileResolver) railwayBare(call *ast.CallExpr, name, brackets string, T, E types.Type, sig *types.Signature) bool {
	var fixed []string
	for i, a := range call.Args[1:] {
		text := r.text(a.Pos(), a.End())
		if i == len(call.Args[1:])-1 && call.Ellipsis.IsValid() {
			text += "..."
		}
		fixed = append(fixed, text)
	}
	return r.railwayLift(call, call.Args[0], T, E, name+brackets, fixed, 0, sig)
}

// railwayLift applies the stage table and emits the combinator call.
func (r *fileResolver) railwayLift(call *ast.CallExpr, head ast.Expr, T, E types.Type, calleeText string, fixed []string, insertAt int, sig *types.Signature) bool {
	// Rule 2: a stage that accepts the Result itself stays a direct call.
	params := sig.Params()
	if insertAt < params.Len() {
		pt := params.At(insertAt).Type()
		if _, _, isRes := r.isResult(pt); isRes || types.AssignableTo(headResultType(T, E, r), pt) {
			return false
		}
	}

	generic := sig.TypeParams() != nil
	res := sig.Results()

	type liftKind int
	const (
		liftBind liftKind = iota
		liftAdapt
		liftMap
		liftTee
	)
	var kind liftKind
	var bindRes types.Type // Bind: the stage's Result return type
	var adaptU types.Type  // adapt: the stage's value return type
	switch {
	case res.Len() == 0:
		kind = liftTee
	case res.Len() == 1:
		if _, resE, isRes := r.isResult(res.At(0).Type()); isRes {
			kind, bindRes = liftBind, res.At(0).Type()
			if _, isTP := types.Unalias(resE).(*types.TypeParam); !isTP && !types.Identical(E, resE) {
				r.errorf(call.Pos(), "cannot bind this stage onto the railway: it returns a Result with error type %s, but the pipeline's error type is %s",
					r.localTypeString(resE), r.localTypeString(E))
				return true
			}
		} else {
			kind = liftMap
		}
	case res.Len() == 2 && isErrorType(res.At(1).Type()):
		kind, adaptU = liftAdapt, res.At(0).Type()
		if !isErrorType(E) {
			r.errorf(call.Pos(), "cannot adapt this (value, error) stage onto a railway whose error type is %s; only railways with error type error adapt Go-shaped stages",
				r.localTypeString(E))
			return true
		}
	default:
		r.errorf(call.Pos(), "cannot lift this stage onto the railway: it returns %d values; railway stages return a Result, a single value, (value, error), or nothing",
			res.Len())
		return true
	}

	resPkg, impOK := r.ensureResultImport()
	if !impOK {
		return true
	}
	headText := r.text(head.Pos(), head.End())

	// The stage argument: the function itself when it can pass through,
	// a closure when extra arguments must wait for the Ok path or the
	// return shape must adapt.
	needClosure := len(fixed) > 0 || kind == liftAdapt
	stage := calleeText
	if needClosure {
		if generic {
			r.errorf(call.Pos(), "cannot lift a generic stage with extra arguments onto the railway; instantiate it explicitly (e.g. %s[int])", calleeText)
			return true
		}
		tText, tErr := r.typeText(T)
		if tErr != nil {
			r.errorf(call.Pos(), "%v", tErr)
			return true
		}
		args := make([]string, 0, len(fixed)+1)
		args = append(args, fixed[:insertAt]...)
		args = append(args, "__gp_p")
		args = append(args, fixed[insertAt:]...)
		callText := calleeText + "(" + strings.Join(args, ", ") + ")"
		switch kind {
		case liftTee:
			stage = fmt.Sprintf("func(__gp_p %s) { %s }", tText, callText)
		case liftAdapt:
			uText, uErr := r.typeText(adaptU)
			if uErr != nil {
				r.errorf(call.Pos(), "%v", uErr)
				return true
			}
			stage = fmt.Sprintf("func(__gp_p %s) %s.Result[%s, error] { return %s.Of(%s) }",
				tText, resPkg, uText, resPkg, callText)
		case liftBind:
			retText, retErr := r.typeText(bindRes)
			if retErr != nil {
				r.errorf(call.Pos(), "%v", retErr)
				return true
			}
			stage = fmt.Sprintf("func(__gp_p %s) %s { return %s }", tText, retText, callText)
		case liftMap:
			uText, uErr := r.typeText(res.At(0).Type())
			if uErr != nil {
				r.errorf(call.Pos(), "%v", uErr)
				return true
			}
			stage = fmt.Sprintf("func(__gp_p %s) %s { return %s }", tText, uText, callText)
		}
	}

	comb := map[liftKind]string{liftBind: "Bind", liftAdapt: "Bind", liftMap: "Map", liftTee: "Tee"}[kind]
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(call.Pos()),
		End:   r.off(call.End()),
		New:   fmt.Sprintf("%s.%s(%s, %s)", resPkg, comb, headText, stage),
	})
	return true
}

// headResultType reconstructs the head's Result type for assignability
// checks against stage parameters.
func headResultType(T, E types.Type, r *fileResolver) types.Type {
	pkg := r.typesByPath[resultPkgPath]
	if pkg == nil {
		return types.Typ[types.Invalid]
	}
	obj, _ := pkg.Scope().Lookup(resultTypeName).(*types.TypeName)
	if obj == nil {
		return types.Typ[types.Invalid]
	}
	named, _ := obj.Type().(*types.Named)
	if named == nil {
		return types.Typ[types.Invalid]
	}
	inst, err := types.Instantiate(nil, named, []types.Type{T, E}, true)
	if err != nil {
		return types.Typ[types.Invalid]
	}
	return inst
}
