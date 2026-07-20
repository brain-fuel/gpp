package resolve

import (
	"fmt"
	"go/ast"
	"go/types"
	"strings"

	"goforge.dev/goplus/internal/lower"
)

// Partial application: a call with top-level `_` arguments lowers to a
// closure with one parameter per placeholder, capturing the callee (when
// it is a value) and every fixed argument exactly once at creation — the
// immediate-application IIFE shape established by methodvalue.go.

// partialCandidate inspects a call for placeholder arguments.
func (r *fileResolver) partialCandidate(call *ast.CallExpr) {
	var placeholders []int
	for i, a := range call.Args {
		if id, ok := a.(*ast.Ident); ok && id.Name == "_" {
			placeholders = append(placeholders, i)
		}
	}
	if len(placeholders) == 0 {
		return
	}
	// Carriers and constructors have their own owners.
	if isCarrierCallee(call.Fun) {
		return
	}
	if r.calleeIsCtor(call.Fun) {
		return // construct.go's placeholder path owns this
	}
	info := r.pkg.TypesInfo
	tv, ok := info.Types[call.Fun]
	if !ok || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
		if r.report {
			r.errorf(call.Pos(), "cannot resolve partial application: %s is not a known function",
				r.text(call.Fun.Pos(), call.Fun.End()))
		}
		return
	}
	if tv.IsType() {
		r.errorf(call.Pos(), "cannot partially apply the conversion %s; write a closure", r.text(call.Fun.Pos(), call.Fun.End()))
		return
	}
	if tv.IsBuiltin() {
		r.errorf(call.Pos(), "cannot partially apply a builtin; write a closure")
		return
	}
	sig, isSig := types.Unalias(tv.Type).(*types.Signature)
	if !isSig {
		if under, ok := tv.Type.Underlying().(*types.Signature); ok {
			sig = under
		} else {
			r.errorf(call.Pos(), "cannot partially apply %s: it is not a function",
				r.text(call.Fun.Pos(), call.Fun.End()))
			return
		}
	}

	// Generic callee: infer type arguments from the fixed arguments.
	targsText := ""
	if sig.TypeParams() != nil && sig.TypeParams().Len() > 0 {
		bound := make([]types.Type, sig.TypeParams().Len())
		tpIndex := map[*types.TypeParam]int{}
		for i := 0; i < sig.TypeParams().Len(); i++ {
			tpIndex[sig.TypeParams().At(i)] = i
		}
		for i, a := range call.Args {
			if i >= len(call.Args) {
				break
			}
			if id, isID := a.(*ast.Ident); isID && id.Name == "_" {
				continue
			}
			atv, aok := info.Types[a]
			if !aok || atv.Type == nil {
				return // wait for the argument to type
			}
			pt := paramTypeAt(sig, i)
			if pt == nil {
				break
			}
			if !unifyTypes(pt, types.Default(atv.Type), tpIndex, bound) {
				break
			}
		}
		var parts []string
		for i, b := range bound {
			if b == nil {
				r.errorf(call.Pos(), "cannot infer the type arguments of %s from its non-placeholder arguments; instantiate it: %s[...](%s)",
					r.text(call.Fun.Pos(), call.Fun.End()), r.text(call.Fun.Pos(), call.Fun.End()), placeholderCallShape(call, r))
				return
			}
			text, terr := r.typeText(b)
			if terr != nil {
				r.errorf(call.Pos(), "%v", terr)
				return
			}
			_ = i
			parts = append(parts, text)
		}
		targsText = "[" + strings.Join(parts, ", ") + "]"
		inst, err := types.Instantiate(nil, sig, bound, true)
		if err != nil {
			r.errorf(call.Pos(), "instantiating %s: %v", r.text(call.Fun.Pos(), call.Fun.End()), err)
			return
		}
		sig = inst.(*types.Signature)
	}

	// Placeholder in a variadic slot is out of scope for v0.3.0.
	if sig.Variadic() {
		for _, pi := range placeholders {
			if pi >= sig.Params().Len()-1 {
				r.errorf(call.Args[pi].Pos(), "_ cannot stand for a variadic parameter in v0.3.0")
				return
			}
		}
		if call.Ellipsis.IsValid() {
			r.errorf(call.Ellipsis, "cannot partially apply a call that spreads with ... in v0.3.0")
			return
		}
	}

	// Callee handling: pure references are called directly; values (incl.
	// method values, which capture their receiver bind-time) are captured.
	calleeText := r.text(call.Fun.Pos(), call.Fun.End())
	pureRef := isPureFuncRef(info, call.Fun)
	if targsText != "" {
		// Inferred instantiation: rewrite the reference explicitly.
		calleeText += targsText
	}

	r.emitPartial(call, sig, placeholders, calleeText, pureRef)
}

// isCarrierCallee reports whether a callee is any goplus carrier family.
func isCarrierCallee(fun ast.Expr) bool {
	base := fun
	switch fn := fun.(type) {
	case *ast.IndexExpr:
		base = fn.X
	case *ast.IndexListExpr:
		base = fn.X
	}
	id, ok := base.(*ast.Ident)
	return ok && strings.HasPrefix(id.Name, "__gp_")
}

// isPureFuncRef reports whether a callee expression is a side-effect-free
// reference to a function (plain name, package-qualified name, or an
// instantiation of either) — safe to call in the closure body without
// capturing a value first.
func isPureFuncRef(info *types.Info, fun ast.Expr) bool {
	switch fn := fun.(type) {
	case *ast.Ident:
		_, ok := info.Uses[fn].(*types.Func)
		return ok
	case *ast.SelectorExpr:
		if _, isSel := info.Selections[fn]; isSel {
			return false // method value: receiver must be captured
		}
		_, ok := info.Uses[fn.Sel].(*types.Func)
		return ok
	case *ast.IndexExpr:
		return isPureFuncRef(info, fn.X)
	case *ast.IndexListExpr:
		return isPureFuncRef(info, fn.X)
	}
	return false
}

// emitPartial renders the capture-once closure for a partial application.
func (r *fileResolver) emitPartial(call *ast.CallExpr, sig *types.Signature, placeholders []int, calleeText string, pureRef bool) {
	isPlaceholder := map[int]bool{}
	for _, pi := range placeholders {
		isPlaceholder[pi] = true
	}

	var outerParams, outerArgs []string // captures
	var innerParams, innerTypes []string
	var bodyArgs []string
	fail := func(err error) bool {
		if err != nil {
			r.errorf(call.Pos(), "%v", err)
			return true
		}
		return false
	}

	if !pureRef {
		ft, err := r.typeText(sig)
		if fail(err) {
			return
		}
		outerParams = append(outerParams, "__gp_f "+ft)
		outerArgs = append(outerArgs, calleeText)
		calleeText = "__gp_f"
	}
	ci, pi := 0, 0
	for i, a := range call.Args {
		pt := paramTypeAt(sig, i)
		if pt == nil {
			r.errorf(call.Pos(), "too many arguments in partial application")
			return
		}
		tt, err := r.typeText(pt)
		if fail(err) {
			return
		}
		if isPlaceholder[i] {
			name := fmt.Sprintf("__gp_p%d", pi)
			pi++
			innerParams = append(innerParams, name+" "+tt)
			innerTypes = append(innerTypes, tt)
			bodyArgs = append(bodyArgs, name)
			continue
		}
		name := fmt.Sprintf("__gp_c%d", ci)
		ci++
		outerParams = append(outerParams, name+" "+tt)
		outerArgs = append(outerArgs, r.text(a.Pos(), a.End()))
		bodyArgs = append(bodyArgs, name)
	}

	resText := ""
	switch results := sig.Results(); results.Len() {
	case 0:
	case 1:
		tt, err := r.typeText(results.At(0).Type())
		if fail(err) {
			return
		}
		resText = " " + tt
	default:
		var parts []string
		for i := 0; i < results.Len(); i++ {
			tt, err := r.typeText(results.At(i).Type())
			if fail(err) {
				return
			}
			parts = append(parts, tt)
		}
		resText = " (" + strings.Join(parts, ", ") + ")"
	}

	callText := calleeText + "(" + strings.Join(bodyArgs, ", ") + ")"
	body := callText
	if sig.Results().Len() > 0 {
		body = "return " + callText
	}
	inner := fmt.Sprintf("func(%s)%s { %s }", strings.Join(innerParams, ", "), resText, body)
	out := inner
	if len(outerParams) > 0 {
		out = fmt.Sprintf("func(%s) func(%s)%s { return %s }(%s)",
			strings.Join(outerParams, ", "), strings.Join(innerTypes, ", "), resText, inner, strings.Join(outerArgs, ", "))
	}
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(call.Pos()),
		End:   r.off(call.End()),
		New:   out,
	})
}

// paramTypeAt returns the effective parameter type for argument index i
// (variadic-aware); nil when out of range.
func paramTypeAt(sig *types.Signature, i int) types.Type {
	params := sig.Params()
	if sig.Variadic() && i >= params.Len()-1 {
		if s, ok := params.At(params.Len() - 1).Type().(*types.Slice); ok {
			return s.Elem()
		}
		return nil
	}
	if i < params.Len() {
		return params.At(i).Type()
	}
	return nil
}

// calleeIsCtor reports whether a callee names an enum constructor (the
// constructor resolver owns those placeholders).
func (r *fileResolver) calleeIsCtor(fun ast.Expr) bool {
	base := fun
	switch fn := fun.(type) {
	case *ast.IndexExpr:
		base = fn.X
	case *ast.IndexListExpr:
		base = fn.X
	}
	switch fn := base.(type) {
	case *ast.Ident:
		if obj, ok := r.pkg.TypesInfo.Uses[fn].(*types.TypeName); ok && obj.Pkg() != nil {
			if _, isVariant := r.reg.EnumByVariantType(obj.Pkg().Path(), obj.Name()); isVariant {
				return true
			}
		}
		if r.pkg.TypesInfo.Uses[fn] == nil && r.pkg.TypesInfo.Defs[fn] == nil {
			return len(r.reg.EnumsByVariantName(r.pkg.PkgPath, fn.Name)) > 0
		}
	case *ast.SelectorExpr:
		if tn, _ := resolveTypeNameOf(r.pkg.TypesInfo, fn); tn != nil && tn.Pkg() != nil {
			if _, isVariant := r.reg.EnumByVariantType(tn.Pkg().Path(), tn.Name()); isVariant {
				return true
			}
			if _, isEnum := r.reg.LookupEnum(tn.Pkg().Path(), tn.Name()); isEnum {
				return true
			}
		}
		if tn, _ := resolveTypeNameOf(r.pkg.TypesInfo, fn.X); tn != nil && tn.Pkg() != nil {
			if _, isEnum := r.reg.LookupEnum(tn.Pkg().Path(), tn.Name()); isEnum {
				return true
			}
		}
	}
	return false
}

// unifyTypes structurally unifies a (possibly generic) parameter type
// against a concrete argument type, binding type parameters.
func unifyTypes(param, arg types.Type, tpIndex map[*types.TypeParam]int, bound []types.Type) bool {
	param = types.Unalias(param)
	arg = types.Unalias(arg)
	if tp, isTP := param.(*types.TypeParam); isTP {
		i, tracked := tpIndex[tp]
		if !tracked {
			return true
		}
		if bound[i] == nil {
			bound[i] = arg
			return true
		}
		return types.Identical(bound[i], arg)
	}
	switch p := param.(type) {
	case *types.Pointer:
		a, ok := arg.(*types.Pointer)
		return ok && unifyTypes(p.Elem(), a.Elem(), tpIndex, bound)
	case *types.Slice:
		a, ok := arg.(*types.Slice)
		return ok && unifyTypes(p.Elem(), a.Elem(), tpIndex, bound)
	case *types.Array:
		a, ok := arg.(*types.Array)
		return ok && unifyTypes(p.Elem(), a.Elem(), tpIndex, bound)
	case *types.Map:
		a, ok := arg.(*types.Map)
		return ok && unifyTypes(p.Key(), a.Key(), tpIndex, bound) && unifyTypes(p.Elem(), a.Elem(), tpIndex, bound)
	case *types.Chan:
		a, ok := arg.(*types.Chan)
		return ok && unifyTypes(p.Elem(), a.Elem(), tpIndex, bound)
	case *types.Signature:
		a, ok := arg.(*types.Signature)
		if !ok || p.Params().Len() != a.Params().Len() || p.Results().Len() != a.Results().Len() {
			return false
		}
		for i := 0; i < p.Params().Len(); i++ {
			if !unifyTypes(p.Params().At(i).Type(), a.Params().At(i).Type(), tpIndex, bound) {
				return false
			}
		}
		for i := 0; i < p.Results().Len(); i++ {
			if !unifyTypes(p.Results().At(i).Type(), a.Results().At(i).Type(), tpIndex, bound) {
				return false
			}
		}
		return true
	case *types.Named:
		a, ok := arg.(*types.Named)
		if !ok || p.Obj() != a.Obj() {
			return true // different named types: let go/types judge later
		}
		pt, at := p.TypeArgs(), a.TypeArgs()
		if pt == nil || at == nil || pt.Len() != at.Len() {
			return true
		}
		for i := 0; i < pt.Len(); i++ {
			if !unifyTypes(pt.At(i), at.At(i), tpIndex, bound) {
				return false
			}
		}
		return true
	}
	return true
}

// placeholderCallShape re-renders the call's argument list for hints.
func placeholderCallShape(call *ast.CallExpr, r *fileResolver) string {
	var parts []string
	for _, a := range call.Args {
		parts = append(parts, r.text(a.Pos(), a.End()))
	}
	return strings.Join(parts, ", ")
}
