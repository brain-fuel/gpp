package resolve

import (
	"fmt"
	"go/ast"
	"go/types"
	"strings"

	"goforge.dev/goplus/internal/lower"
)

// methodValue lowers an instantiated generic method value, e.g.
//
//	f := s.Map[string]
//
// into a closure over the lowered function with the receiver captured at
// bind time (matching Go's method value semantics):
//
//	f := func(__gp_recv Stack[int]) func(func(int) string) Stack[string] {
//	        return func(p0 func(int) string) Stack[string] {
//	                return StackMap[int, string](__gp_recv, p0)
//	        }
//	}(s)
func (r *fileResolver) methodValue(idx ast.Expr, sel *ast.SelectorExpr, typeArgs []ast.Expr, h *hit, tv types.TypeAndValue) {
	if len(typeArgs) != h.method.NumMethodTParams {
		r.errorf(sel.Pos(), "method value %s.%s requires all %d type arguments, got %d",
			exprString(sel.X), sel.Sel.Name, h.method.NumMethodTParams, len(typeArgs))
		return
	}
	recvArg, ok := r.receiverArg(sel, h, tv)
	if !ok {
		return
	}
	funcRef, ok := r.funcRef(sel.Pos(), h.method)
	if !ok {
		return
	}
	recvTargs, ok := r.receiverTypeArgs(sel.Pos(), h)
	if !ok {
		return
	}

	// The lowered function's generic signature, from type information.
	pkgTypes, okPkg := r.typesByPath[h.method.PkgPath]
	if !okPkg {
		r.errorf(sel.Pos(), "internal error: no type information for package %s", h.method.PkgPath)
		return
	}
	obj := pkgTypes.Scope().Lookup(h.method.FuncName)
	if obj == nil {
		r.errorf(sel.Pos(), "internal error: lowered function %s not found in %s", h.method.FuncName, h.method.PkgPath)
		return
	}
	sig, okSig := obj.Type().(*types.Signature)
	if !okSig {
		r.errorf(sel.Pos(), "internal error: %s.%s is not a function", h.method.PkgPath, h.method.FuncName)
		return
	}

	// Assemble real type arguments: the receiver's, then the explicit
	// ones evaluated in this file's scope.
	var targs []types.Type
	if ta := h.named.TypeArgs(); ta != nil {
		for i := 0; i < ta.Len(); i++ {
			targs = append(targs, ta.At(i))
		}
	}
	explicitTexts := make([]string, len(typeArgs))
	for i, texpr := range typeArgs {
		text := r.text(texpr.Pos(), texpr.End())
		explicitTexts[i] = text
		tvv, err := types.Eval(r.pkg.Fset, r.pkg.Types, sel.Pos(), text)
		if err != nil || tvv.Type == nil {
			r.errorf(texpr.Pos(), "cannot resolve type argument %s", text)
			return
		}
		targs = append(targs, tvv.Type)
	}
	isig := sig
	if len(targs) > 0 {
		inst, err := types.Instantiate(nil, sig, targs, true)
		if err != nil {
			r.errorf(sel.Pos(), "instantiating %s.%s: %v", exprString(sel.X), sel.Sel.Name, err)
			return
		}
		isig = inst.(*types.Signature)
	}
	params := isig.Params()
	if params.Len() == 0 {
		r.errorf(sel.Pos(), "internal error: lowered function %s has no receiver parameter", h.method.FuncName)
		return
	}

	recvParamType, terr := r.typeText(params.At(0).Type())
	if terr != nil {
		r.errorf(sel.Pos(), "%v", terr)
		return
	}
	var paramDecls, paramTypes, callArgs []string
	for i := 1; i < params.Len(); i++ {
		name := fmt.Sprintf("p%d", i-1)
		t := params.At(i).Type()
		if isig.Variadic() && i == params.Len()-1 {
			elem, terr := r.typeText(t.(*types.Slice).Elem())
			if terr != nil {
				r.errorf(sel.Pos(), "%v", terr)
				return
			}
			paramDecls = append(paramDecls, name+" ..."+elem)
			paramTypes = append(paramTypes, "..."+elem)
			callArgs = append(callArgs, name+"...")
			continue
		}
		tt, terr := r.typeText(t)
		if terr != nil {
			r.errorf(sel.Pos(), "%v", terr)
			return
		}
		paramDecls = append(paramDecls, name+" "+tt)
		paramTypes = append(paramTypes, tt)
		callArgs = append(callArgs, name)
	}

	resText := ""
	switch results := isig.Results(); results.Len() {
	case 0:
	case 1:
		tt, terr := r.typeText(results.At(0).Type())
		if terr != nil {
			r.errorf(sel.Pos(), "%v", terr)
			return
		}
		resText = " " + tt
	default:
		parts := make([]string, results.Len())
		for i := 0; i < results.Len(); i++ {
			tt, terr := r.typeText(results.At(i).Type())
			if terr != nil {
				r.errorf(sel.Pos(), "%v", terr)
				return
			}
			parts[i] = tt
		}
		resText = " (" + strings.Join(parts, ", ") + ")"
	}

	allTargs := ""
	if combined := append(append([]string{}, recvTargs...), explicitTexts...); len(combined) > 0 {
		allTargs = "[" + strings.Join(combined, ", ") + "]"
	}
	call := funcRef + allTargs + "(__gp_recv"
	if len(callArgs) > 0 {
		call += ", " + strings.Join(callArgs, ", ")
	}
	call += ")"
	body := call
	if isig.Results().Len() > 0 {
		body = "return " + call
	}
	inner := fmt.Sprintf("func(%s)%s { %s }", strings.Join(paramDecls, ", "), resText, body)
	outer := fmt.Sprintf("func(__gp_recv %s) func(%s)%s { return %s }(%s)",
		recvParamType, strings.Join(paramTypes, ", "), resText, inner, recvArg)

	r.edits = append(r.edits, lower.Edit{
		Start: r.off(idx.Pos()),
		End:   r.off(idx.End()),
		New:   outer,
	})
}
