package resolve

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/types"
	"strings"

	"goforge.dev/goplus/internal/lower"
)

// Composition. Pass 1 lowers `f >>> g >>> h` to the carrier
// `__gp_comp(f, g, h)`; once every operand's type is known, the chain
// lowers to one flat capture-once IIFE. The first operand may take any
// parameters (one result); each later operand takes exactly one parameter
// and returns one result. Constructor operands (`double >>> Some`) infer
// their type arguments from the incoming type.

type composeOp struct {
	expr ast.Expr
	text string
	sig  *types.Signature // nil for ctor operands until inferred
	ctor *ctorUse         // non-nil for constructor operands
}

// composeCandidate inspects a compose carrier call.
func (r *fileResolver) composeCandidate(call *ast.CallExpr) {
	fn, ok := call.Fun.(*ast.Ident)
	if !ok || fn.Name != lower.ComposeCarrier || len(call.Args) < 2 {
		return
	}
	info := r.pkg.TypesInfo

	ops := make([]*composeOp, len(call.Args))
	for i, a := range call.Args {
		op := &composeOp{expr: a, text: r.text(a.Pos(), a.End())}
		ops[i] = op
		// Constructor operands first: a variant name resolves as a TYPE
		// in the shadow, but the constructor reading owns it here.
		if cands := r.recognizeCtors(a); len(cands) == 1 {
			op.ctor = cands[0]
			continue
		} else if len(cands) > 1 {
			r.errorf(a.Pos(), "constructor %s is ambiguous as a >>> operand; qualify it: %s.%s",
				cands[0].variant.Name, cands[0].enum.Name, cands[0].variant.Name)
			return
		}
		tv, typed := info.Types[a]
		if typed && tv.Type != nil && tv.Type != types.Typ[types.Invalid] {
			if tv.IsType() {
				r.errorf(a.Pos(), "the operands of >>> must be function values; %s is a type", op.text)
				return
			}
			if tup, isTuple := tv.Type.(*types.Tuple); isTuple {
				r.errorf(a.Pos(), "the operands of >>> must be single values; %s produces %d results", op.text, tup.Len())
				return
			}
			sig, isSig := types.Unalias(tv.Type).(*types.Signature)
			if !isSig {
				if under, uok := tv.Type.Underlying().(*types.Signature); uok {
					sig = under
					isSig = true
				}
			}
			if !isSig {
				r.errorf(a.Pos(), "the operands of >>> must be function values; %s has type %s", op.text, r.localTypeString(tv.Type))
				return
			}
			if sig.TypeParams() != nil && sig.TypeParams().Len() > 0 {
				r.errorf(a.Pos(), "cannot use generic function %s as a >>> operand without instantiation (write %s[...])", op.text, op.text)
				return
			}
			op.sig = sig
			continue
		}
		if r.report {
			r.errorf(a.Pos(), "cannot resolve the operands of >>>: the type of %s is unknown", op.text)
		}
		return
	}

	// Walk the chain: first operand fixes the parameters.
	first := ops[0]
	if first.ctor != nil {
		r.errorf(first.expr.Pos(), "a constructor cannot be the first operand of >>> in v0.3.0; wrap it in a function")
		return
	}
	if first.sig.Results().Len() != 1 {
		r.errorf(first.expr.Pos(), "the first operand of >>> must return exactly one result; %s returns %d",
			first.text, first.sig.Results().Len())
		return
	}
	current := first.sig.Results().At(0).Type()

	// Later operands: unary, single result (or an inferred constructor).
	for _, op := range ops[1:] {
		if op.ctor != nil {
			if !r.inferComposeCtor(op, current) {
				return
			}
		} else {
			if op.sig.Params().Len() != 1 || op.sig.Variadic() || op.sig.Results().Len() != 1 {
				r.errorf(op.expr.Pos(), "a non-first operand of >>> must take exactly one parameter and return one result; %s is %s",
					op.text, r.localTypeString(op.sig))
				return
			}
			if !types.AssignableTo(current, op.sig.Params().At(0).Type()) {
				r.errorf(op.expr.Pos(), "cannot compose: the previous operand returns %s but %s takes %s",
					r.localTypeString(current), op.text, r.localTypeString(op.sig.Params().At(0).Type()))
				return
			}
		}
		current = op.sig.Results().At(0).Type()
	}

	r.emitCompose(call, ops)
}

// inferComposeCtor turns a constructor operand into a closure taking the
// incoming type, filling op.text and op.sig.
func (r *fileResolver) inferComposeCtor(op *composeOp, incoming types.Type) bool {
	use := op.ctor
	e, v := use.enum, use.variant
	if len(v.Params) != 1 {
		r.errorf(op.expr.Pos(), "constructor %s takes %d arguments and cannot be a >>> operand (which receives one value)",
			v.Name, len(v.Params))
		return false
	}
	// Infer type args: explicit instantiation, else unify the declared
	// parameter type against the incoming type.
	var targs []string
	var boundTypes []types.Type // complete inferred type args, when available
	if len(use.explicit) > 0 {
		got, ok := r.explicitTargs(use)
		if !ok {
			return false
		}
		targs = got
	} else {
		tparamIndex := map[string]int{}
		for i, n := range e.TParams {
			tparamIndex[n] = i
		}
		bound := make([]types.Type, len(e.TParams))
		declExpr, err := parser.ParseExpr(v.Params[0].Type)
		if err == nil {
			if !r.unifyDecl(declExpr, incoming, tparamIndex, bound) {
				r.errorf(op.expr.Pos(), "cannot compose: %s cannot accept %s", v.Name, r.localTypeString(incoming))
				return false
			}
		}
		targs = make([]string, len(e.TParams))
		if v.ResultArgs != nil {
			tset := tparamSetOf(e)
			for i, arg := range v.ResultArgs {
				if !textHasTParam(arg, tset) {
					targs[i] = arg
				}
			}
		}
		if use.railE != nil && len(bound) == 2 && bound[1] == nil {
			bound[1] = use.railE // expected-result inference (kleisli rail)
		}
		for i := range targs {
			if targs[i] != "" {
				continue
			}
			if bound[i] == nil {
				r.errorf(op.expr.Pos(), "cannot infer the type arguments of constructor %s from the incoming %s; instantiate it: %s[...]",
					v.Name, r.localTypeString(incoming), v.Name)
				return false
			}
			text, terr := r.typeText(bound[i])
			if terr != nil {
				r.errorf(op.expr.Pos(), "%v", terr)
				return false
			}
			targs[i] = text
		}
		complete := len(bound) == len(e.TParams)
		for _, b := range bound {
			if b == nil {
				complete = false
			}
		}
		if complete {
			boundTypes = bound
		}
	}

	litType, ok := r.ctorTypeText(use, targs)
	if !ok {
		return false
	}
	enumText := e.Name
	if use.pkgAlias != "" {
		enumText = use.pkgAlias + "." + enumText
	} else if e.PkgPath != r.pkg.PkgPath {
		alias, aok := r.importName(e.PkgPath)
		if !aok {
			r.errorf(op.expr.Pos(), "using constructor %s requires importing %q", v.Name, e.PkgPath)
			return false
		}
		enumText = alias + "." + enumText
	}
	if len(e.TParams) > 0 {
		enumText += "[" + strings.Join(targs, ", ") + "]"
	}
	subst, sok := variantSubst(e, v, targs)
	if !sok {
		r.errorf(op.expr.Pos(), "cannot infer the type arguments of constructor %s; instantiate it: %s[...]", v.Name, v.Name)
		return false
	}
	paramText, serr := substTypeTextLite(v.Params[0].Type, subst)
	if serr != nil {
		r.errorf(op.expr.Pos(), "internal error: rendering %s's field type: %v", v.Name, serr)
		return false
	}
	op.text = fmt.Sprintf("func(__gp_x %s) %s { return %s{%s: __gp_x} }",
		paramText, enumText, litType, v.Params[0].FieldName)

	// Synthesize the operand's signature for the chain walk.
	incomingParam := types.NewVar(0, nil, "", incoming)
	result := r.evalInPkg(r.pkg.PkgPath, enumText)
	if result == nil && boundTypes != nil {
		// Cross-package enums: evalInPkg cannot see file-scoped import
		// names, so instantiate from the loaded package directly.
		if pkg := r.typesByPath[e.PkgPath]; pkg != nil {
			if tn, isTN := pkg.Scope().Lookup(e.Name).(*types.TypeName); isTN {
				if named, isNamed := tn.Type().(*types.Named); isNamed {
					if inst, err := types.Instantiate(nil, named, boundTypes, true); err == nil {
						result = inst
					}
				}
			}
		}
	}
	if result == nil {
		result = incoming // fallback: only used for chain-walk continuation
	}
	op.sig = types.NewSignatureType(nil, nil, nil,
		types.NewTuple(incomingParam), types.NewTuple(types.NewVar(0, nil, "", result)), false)
	return true
}

// emitCompose renders the flat capture-once IIFE.
func (r *fileResolver) emitCompose(call *ast.CallExpr, ops []*composeOp) {
	var outerParams, outerArgs []string
	fail := func(err error) bool {
		if err != nil {
			r.errorf(call.Pos(), "%v", err)
			return true
		}
		return false
	}
	for i, op := range ops {
		ft, err := r.typeText(op.sig)
		if fail(err) {
			return
		}
		outerParams = append(outerParams, fmt.Sprintf("__gp_f%d %s", i, ft))
		outerArgs = append(outerArgs, op.text)
	}

	first := ops[0].sig
	var innerParams, innerTypes, callArgs []string
	for i := 0; i < first.Params().Len(); i++ {
		t := first.Params().At(i).Type()
		name := fmt.Sprintf("__gp_a%d", i)
		if first.Variadic() && i == first.Params().Len()-1 {
			elem, err := r.typeText(t.(*types.Slice).Elem())
			if fail(err) {
				return
			}
			innerParams = append(innerParams, name+" ..."+elem)
			innerTypes = append(innerTypes, "..."+elem)
			callArgs = append(callArgs, name+"...")
			continue
		}
		tt, err := r.typeText(t)
		if fail(err) {
			return
		}
		innerParams = append(innerParams, name+" "+tt)
		innerTypes = append(innerTypes, tt)
		callArgs = append(callArgs, name)
	}
	lastSig := ops[len(ops)-1].sig
	resText, err := r.typeText(lastSig.Results().At(0).Type())
	if fail(err) {
		return
	}

	body := "__gp_f0(" + strings.Join(callArgs, ", ") + ")"
	for i := 1; i < len(ops); i++ {
		body = fmt.Sprintf("__gp_f%d(%s)", i, body)
	}
	out := fmt.Sprintf("func(%s) func(%s) %s { return func(%s) %s { return %s } }(%s)",
		strings.Join(outerParams, ", "), strings.Join(innerTypes, ", "), resText,
		strings.Join(innerParams, ", "), resText, body, strings.Join(outerArgs, ", "))
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(call.Pos()),
		End:   r.off(call.End()),
		New:   out,
	})
}
