package resolve

import (
	"fmt"
	"go/ast"
	"go/types"
	"strings"

	"goforge.dev/goplus/internal/lower"
)

// Kleisli composition (v0.4.0). Pass 1 lowers a mixed `>=>` / `>>>` chain
// to `__gp_kcomp_<kinds>(f, g, h)` with one kind letter per link ('k'
// for >=>, 'c' for >>>). The chain folds left-to-right with track state:
// the rail opens at the first failure-capable operand (returning a Result
// or (U, error)); after that, `>=>` links lift plain operands (Map/Tee),
// bind Result operands, and adapt (U, error) operands, while `>>>` links
// demand an operand that accepts the Result itself. Emission is one flat
// capture-once IIFE threading std/result combinators.

// kstep is one link's emission plan.
type kstep struct {
	kind   byte   // 'f' fn-apply, 'b' Bind, 'm' Map, 't' Tee, 'a' adapt, 'o' Of-entry
	adaptU string // adapt: the operand's value type text
	adaptT string // adapt: the operand's parameter type text
}

// kcompCandidate inspects a kleisli carrier call.
func (r *fileResolver) kcompCandidate(call *ast.CallExpr) {
	fn, ok := call.Fun.(*ast.Ident)
	if !ok {
		return
	}
	kinds, found := strings.CutPrefix(fn.Name, lower.KleisliCarrierPrefix)
	if !found || len(call.Args) < 2 || len(kinds) != len(call.Args)-1 {
		return
	}
	info := r.pkg.TypesInfo

	// Operand typing, mirroring composeCandidate; kleisli operands may
	// also return (U, error) or nothing.
	ops := make([]*composeOp, len(call.Args))
	for i, a := range call.Args {
		op := &composeOp{expr: a, text: r.text(a.Pos(), a.End())}
		ops[i] = op
		if cands := r.recognizeCtors(a); len(cands) == 1 {
			op.ctor = cands[0]
			continue
		} else if len(cands) > 1 {
			r.errorf(a.Pos(), "constructor %s is ambiguous as a >=> operand; qualify it: %s.%s",
				cands[0].variant.Name, cands[0].enum.Name, cands[0].variant.Name)
			return
		}
		tv, typed := info.Types[a]
		if typed && tv.Type != nil && tv.Type != types.Typ[types.Invalid] {
			if tv.IsType() {
				r.errorf(a.Pos(), "the operands of >=> must be function values; %s is a type", op.text)
				return
			}
			if tup, isTuple := tv.Type.(*types.Tuple); isTuple {
				r.errorf(a.Pos(), "the operands of >=> must be single values; %s produces %d results", op.text, tup.Len())
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
				r.errorf(a.Pos(), "the operands of >=> must be function values; %s has type %s", op.text, r.localTypeString(tv.Type))
				return
			}
			if sig.TypeParams() != nil && sig.TypeParams().Len() > 0 {
				r.errorf(a.Pos(), "cannot use generic function %s as a >=> operand without instantiation (write %s[...])", op.text, op.text)
				return
			}
			op.sig = sig
			continue
		}
		if r.report {
			r.errorf(a.Pos(), "cannot resolve the operands of >=>: the type of %s is unknown", op.text)
		}
		return
	}

	// First operand fixes the parameters. A (U, error) first operand
	// enters the rail through result.Of.
	first := ops[0]
	if first.ctor != nil {
		r.errorf(first.expr.Pos(), "a constructor cannot be the first operand of a composition; wrap it in a function")
		return
	}
	steps := make([]kstep, 1, len(ops))
	canFail := false
	var cur types.Type
	fres := first.sig.Results()
	switch {
	case fres.Len() == 1:
		steps[0] = kstep{kind: 'f'}
		cur = fres.At(0).Type()
		if _, _, isRes := r.isResult(cur); isRes {
			canFail = true
		}
	case fres.Len() == 2 && isErrorType(fres.At(1).Type()):
		if !r.requireResultPkg(call.Pos()) {
			return
		}
		steps[0] = kstep{kind: 'o'}
		cur = r.resultOf(fres.At(0).Type(), types.Universe.Lookup("error").Type())
		canFail = true
	default:
		r.errorf(first.expr.Pos(), "the first operand of a >=> chain must return one result or (value, error); %s returns %d results",
			first.text, fres.Len())
		return
	}

	for i, op := range ops[1:] {
		kleisliLink := kinds[i] == 'k'
		T, E, onRail := r.isResult(cur)

		if op.ctor != nil {
			incoming := cur
			var railE types.Type
			if onRail && kleisliLink {
				incoming, railE = T, E
			}
			if !r.inferComposeCtorRail(op, incoming, railE) {
				return
			}
		}

		if onRail && !kleisliLink {
			// >>> after the rail opened: the operand must accept the
			// Result itself.
			if op.sig.Params().Len() != 1 || op.sig.Variadic() || !types.AssignableTo(cur, op.sig.Params().At(0).Type()) {
				r.errorf(op.expr.Pos(), "after a failure-capable operand, >>> requires a stage that accepts the %s; use >=> to stay on the railway",
					r.localTypeString(cur))
				return
			}
			if op.sig.Results().Len() != 1 {
				r.errorf(op.expr.Pos(), "a non-first operand of >>> must take exactly one parameter and return one result; %s is %s",
					op.text, r.localTypeString(op.sig))
				return
			}
			steps = append(steps, kstep{kind: 'f'})
			cur = op.sig.Results().At(0).Type()
			if _, _, isRes := r.isResult(cur); isRes {
				canFail = true
			}
			continue
		}

		if !onRail {
			// Plain track: both link kinds compose directly; a (U, error)
			// operand on a >=> link opens the rail through result.Of.
			if op.sig.Params().Len() != 1 || op.sig.Variadic() {
				r.errorf(op.expr.Pos(), "a non-first operand of a composition must take exactly one parameter; %s is %s",
					op.text, r.localTypeString(op.sig))
				return
			}
			if !types.AssignableTo(cur, op.sig.Params().At(0).Type()) {
				r.errorf(op.expr.Pos(), "cannot compose: the previous operand returns %s but %s takes %s",
					r.localTypeString(cur), op.text, r.localTypeString(op.sig.Params().At(0).Type()))
				return
			}
			res := op.sig.Results()
			switch {
			case res.Len() == 1:
				steps = append(steps, kstep{kind: 'f'})
				cur = res.At(0).Type()
				if _, _, isRes := r.isResult(cur); isRes {
					canFail = true
				}
			case res.Len() == 2 && isErrorType(res.At(1).Type()) && kleisliLink:
				if !r.requireResultPkg(call.Pos()) {
					return
				}
				steps = append(steps, kstep{kind: 'o'})
				cur = r.resultOf(res.At(0).Type(), types.Universe.Lookup("error").Type())
				canFail = true
			default:
				r.errorf(op.expr.Pos(), "a non-first operand of a composition must return one result (or (value, error) on a >=> link); %s is %s",
					op.text, r.localTypeString(op.sig))
				return
			}
			continue
		}

		// Rail track, >=> link: lift by shape.
		if op.sig.Params().Len() != 1 || op.sig.Variadic() {
			r.errorf(op.expr.Pos(), "a >=> operand must take exactly one parameter; %s is %s",
				op.text, r.localTypeString(op.sig))
			return
		}
		if !types.AssignableTo(T, op.sig.Params().At(0).Type()) {
			r.errorf(op.expr.Pos(), "cannot compose onto the railway: the flowing value is %s but %s takes %s",
				r.localTypeString(T), op.text, r.localTypeString(op.sig.Params().At(0).Type()))
			return
		}
		res := op.sig.Results()
		switch {
		case res.Len() == 0:
			steps = append(steps, kstep{kind: 't'})
		case res.Len() == 1:
			if _, resE, isRes := r.isResult(res.At(0).Type()); isRes {
				if !types.Identical(E, resE) {
					r.errorf(op.expr.Pos(), "cannot bind this stage onto the railway: it returns a Result with error type %s, but the chain's error type is %s",
						r.localTypeString(resE), r.localTypeString(E))
					return
				}
				steps = append(steps, kstep{kind: 'b'})
				cur = res.At(0).Type()
				canFail = true
			} else {
				steps = append(steps, kstep{kind: 'm'})
				cur = r.resultOf(res.At(0).Type(), E)
			}
		case res.Len() == 2 && isErrorType(res.At(1).Type()):
			if !isErrorType(E) {
				r.errorf(op.expr.Pos(), "cannot adapt this (value, error) stage onto a railway whose error type is %s; only railways with error type error adapt Go-shaped stages",
					r.localTypeString(E))
				return
			}
			uText, uErr := r.typeText(res.At(0).Type())
			tText, tErr := r.typeText(T)
			if uErr != nil || tErr != nil {
				if uErr == nil {
					uErr = tErr
				}
				r.errorf(op.expr.Pos(), "%v", uErr)
				return
			}
			steps = append(steps, kstep{kind: 'a', adaptU: uText, adaptT: tText})
			cur = r.resultOf(res.At(0).Type(), E)
			canFail = true
		default:
			r.errorf(op.expr.Pos(), "cannot lift this stage onto the railway: it returns %d values; railway stages return a Result, a single value, (value, error), or nothing",
				res.Len())
			return
		}
	}

	if !canFail {
		r.errorf(call.Pos(), "no operand of this >=> chain can fail; use >>> for plain composition")
		return
	}
	r.emitKleisli(call, ops, steps, cur)
}

// resultOf instantiates Result[T, E] for chain-walk continuation.
func (r *fileResolver) resultOf(T, E types.Type) types.Type {
	return headResultType(T, E, r)
}

// emitKleisli renders the flat capture-once IIFE threading combinators.
func (r *fileResolver) emitKleisli(call *ast.CallExpr, ops []*composeOp, steps []kstep, final types.Type) {
	resPkg, impOK := r.ensureResultImport()
	if !impOK {
		return
	}
	fail := func(err error) bool {
		if err != nil {
			r.errorf(call.Pos(), "%v", err)
			return true
		}
		return false
	}
	var outerParams, outerArgs []string
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
	resText, err := r.typeText(final)
	if fail(err) {
		return
	}

	var body string
	firstCall := fmt.Sprintf("__gp_f0(%s)", strings.Join(callArgs, ", "))
	if steps[0].kind == 'o' {
		body = fmt.Sprintf("%s.Of(%s)", resPkg, firstCall)
	} else {
		body = firstCall
	}
	for i := 1; i < len(ops); i++ {
		f := fmt.Sprintf("__gp_f%d", i)
		switch steps[i].kind {
		case 'f':
			body = fmt.Sprintf("%s(%s)", f, body)
		case 'b':
			body = fmt.Sprintf("%s.Bind(%s, %s)", resPkg, body, f)
		case 'm':
			body = fmt.Sprintf("%s.Map(%s, %s)", resPkg, body, f)
		case 't':
			body = fmt.Sprintf("%s.Tee(%s, %s)", resPkg, body, f)
		case 'a':
			body = fmt.Sprintf("%s.Bind(%s, func(__gp_p %s) %s.Result[%s, error] { return %s.Of(%s(__gp_p)) })",
				resPkg, body, steps[i].adaptT, resPkg, steps[i].adaptU, resPkg, f)
		case 'o':
			body = fmt.Sprintf("%s.Of(%s(%s))", resPkg, f, body)
		}
	}
	out := fmt.Sprintf("func(%s) func(%s) %s { return func(%s) %s { return %s } }(%s)",
		strings.Join(outerParams, ", "), strings.Join(innerTypes, ", "), resText,
		strings.Join(innerParams, ", "), resText, body, strings.Join(outerArgs, ", "))
	r.edits = append(r.edits, lower.Edit{Start: r.off(call.Pos()), End: r.off(call.End()), New: out})
}

// inferComposeCtorRail extends inferComposeCtor with expected-result
// inference: on a railway link, a Result constructor's unbound error
// parameter binds to the chain's error type.
func (r *fileResolver) inferComposeCtorRail(op *composeOp, incoming, railE types.Type) bool {
	if railE != nil && op.ctor.enum.PkgPath == resultPkgPath && op.ctor.enum.Name == resultTypeName {
		op.ctor.railE = railE
	}
	return r.inferComposeCtor(op, incoming)
}
