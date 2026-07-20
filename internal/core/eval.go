package core

import (
	"fmt"
	"math/big"
)

// Evaluator normalizes terms by evaluation. Total functions unfold when
// their control path is decidable; a call whose body sticks on a
// neutral conditional or match becomes a neutral NCall — the standard
// normal form for pattern-matching definitions applied to symbols. Defs
// are termination-checked before they reach the evaluator, but a fuel
// counter guards against internal bugs anyway.
type Evaluator struct {
	Defs Defs
	Fuel int // remaining steps; Eval errors at 0
	// Permissive: calls to unknown definitions become neutral instead of
	// erroring (symbolic guard analysis).
	Permissive bool
}

// NewEvaluator builds an evaluator with the default fuel budget.
func NewEvaluator(defs Defs) *Evaluator {
	return &Evaluator{Defs: defs, Fuel: 1 << 20}
}

// Eval normalizes t under env.
func (ev *Evaluator) Eval(t Term, env Env) (Value, error) {
	ev.Fuel--
	if ev.Fuel <= 0 {
		return nil, fmt.Errorf("goplus internal: evaluation fuel exhausted (non-terminating total function?)")
	}
	switch x := t.(type) {
	case Var:
		if v, ok := env[x.Name]; ok {
			return v, nil
		}
		return nil, fmt.Errorf("goplus internal: unbound variable %s", x.Name)
	case Nat:
		return linConst(x.N), nil
	case Prim:
		args := make([]VLin, len(x.Args))
		for i, a := range x.Args {
			v, err := ev.Eval(a, env)
			if err != nil {
				return nil, err
			}
			args[i] = asLin(v)
		}
		switch x.Op {
		case "+":
			out := args[0]
			for _, a := range args[1:] {
				out = linAdd(out, a, 1)
			}
			return out, nil
		case "-":
			out := args[0]
			for _, a := range args[1:] {
				out = linAdd(out, a, -1)
			}
			return out, nil
		case "*":
			out := args[0]
			for _, a := range args[1:] {
				out = linMul(out, a)
			}
			return out, nil
		}
		return nil, fmt.Errorf("goplus internal: unknown primitive %q", x.Op)
	case Ctor:
		args := make([]Value, len(x.Args))
		for i, a := range x.Args {
			v, err := ev.Eval(a, env)
			if err != nil {
				return nil, err
			}
			args[i] = v
		}
		return VCtor{Type: x.Type, Name: x.Name, Args: args}, nil
	case Call:
		args := make([]Value, len(x.Args))
		for i, a := range x.Args {
			v, err := ev.Eval(a, env)
			if err != nil {
				return nil, err
			}
			args[i] = v
		}
		def, ok := ev.Defs[x.Fn]
		if !ok {
			if ev.Permissive {
				return VNeu{N: NCall{Fn: x.Fn, Args: args}}, nil
			}
			return nil, fmt.Errorf("goplus internal: call to unknown total function %s", x.Fn)
		}
		if len(args) != len(def.Params) {
			return nil, fmt.Errorf("goplus internal: %s expects %d arguments, got %d", x.Fn, len(def.Params), len(args))
		}
		inner := make(Env, len(args))
		for i, p := range def.Params {
			inner[p] = args[i]
		}
		v, err := ev.Eval(def.Body, inner)
		if err != nil {
			return nil, err
		}
		if isStuckRoot(v) {
			return VNeu{N: NCall{Fn: x.Fn, Args: args}}, nil
		}
		return v, nil
	case If:
		l, err := ev.Eval(x.L, env)
		if err != nil {
			return nil, err
		}
		r, err := ev.Eval(x.R, env)
		if err != nil {
			return nil, err
		}
		ll, rr := asLin(l), asLin(r)
		if ground(ll) && ground(rr) {
			if compareGround(x.Op, ll.Const, rr.Const) {
				return ev.Eval(x.Then, env)
			}
			return ev.Eval(x.Else, env)
		}
		// Same canonical form decides == and <= without groundness.
		if diff := linAdd(ll, rr, -1); ground(diff) && diff.Const.Sign() == 0 {
			switch x.Op {
			case "==", "<=", ">=":
				return ev.Eval(x.Then, env)
			case "!=", "<", ">":
				return ev.Eval(x.Else, env)
			}
		}
		return VNeu{N: NIf{Op: x.Op, L: l, R: r, Then: x.Then, Else: x.Else, Env: env}}, nil
	case MatchT:
		s, err := ev.Eval(x.Scrut, env)
		if err != nil {
			return nil, err
		}
		switch sv := s.(type) {
		case VCtor:
			for _, arm := range x.Arms {
				if arm.Ctor != sv.Name && arm.Ctor != "_" {
					continue
				}
				inner := env.clone()
				if arm.Ctor != "_" {
					if len(arm.Binds) != len(sv.Args) {
						return nil, fmt.Errorf("goplus internal: arm %s binds %d fields of %d", arm.Ctor, len(arm.Binds), len(sv.Args))
					}
					for i, b := range arm.Binds {
						inner[b] = sv.Args[i]
					}
				}
				return ev.Eval(arm.Body, inner)
			}
			return nil, fmt.Errorf("goplus internal: no arm for constructor %s", sv.Name)
		case VNeu:
			arms := make([]NArm, len(x.Arms))
			for i, a := range x.Arms {
				arms[i] = NArm{Ctor: a.Ctor, Binds: a.Binds, Body: a.Body, Env: env}
			}
			return VNeu{N: NMatch{Scrut: sv.N, Arms: arms}}, nil
		default:
			return nil, fmt.Errorf("goplus internal: match scrutinee is not data: %s", s)
		}
	}
	return nil, fmt.Errorf("goplus internal: unknown term %T", t)
}

// isStuckRoot reports whether a value is stuck at its root on control
// flow (the shapes a call collapses to a neutral call for).
func isStuckRoot(v Value) bool {
	n, ok := v.(VNeu)
	if !ok {
		return false
	}
	switch n.N.(type) {
	case NIf, NMatch:
		return true
	}
	return false
}

func compareGround(op string, a, b *big.Int) bool {
	c := a.Cmp(b)
	switch op {
	case "==":
		return c == 0
	case "!=":
		return c != 0
	case "<":
		return c < 0
	case "<=":
		return c <= 0
	case ">":
		return c > 0
	case ">=":
		return c >= 0
	}
	return false
}

// EvalClosed normalizes a closed term with fresh default fuel.
func EvalClosed(defs Defs, t Term) (Value, error) {
	return NewEvaluator(defs).Eval(t, Env{})
}

// bigOne is shared by canonical-form helpers.
var bigOne = big.NewInt(1)

// EvalSymbolic normalizes a term with unknown calls left neutral.
func EvalSymbolic(t Term, env Env) (Value, error) {
	ev := &Evaluator{Fuel: 1 << 16, Permissive: true}
	return ev.Eval(t, env)
}

// LinNeverZero reports whether a - b can NEVER be zero given every atom
// is a non-negative nat: a positive constant with non-negative
// coefficients (or the mirror) has no root.
func LinNeverZero(a, b Value) bool {
	diff := linAdd(asLin(a), asLin(b), -1)
	if diff.Const.Sign() > 0 {
		for _, c := range diff.Coef {
			if c.Sign() < 0 {
				return false
			}
		}
		return true
	}
	if diff.Const.Sign() < 0 {
		for _, c := range diff.Coef {
			if c.Sign() > 0 {
				return false
			}
		}
		return true
	}
	return false
}
