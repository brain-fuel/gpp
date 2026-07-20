package core

import (
	"fmt"
	"go/ast"
	"math/big"
)

// Subtraction obligations (v0.7.0): nat is closed under + and *, but
// a - b is admissible only where the path proves a ≥ b. Obligations are
// discharged symbolically — variables and opaque subterms (calls,
// products) become atoms, if-conditions become hypotheses along each
// branch — through the linear-arithmetic decider.

// CheckSubtractions walks def's body and errors on the first
// subtraction the path facts cannot justify.
func CheckSubtractions(def *Def) error {
	return walkOblig(def.Body, nil)
}

func walkOblig(t Term, hyps []Fact) error {
	switch x := t.(type) {
	case Var, Nat:
		return nil
	case Prim:
		for _, a := range x.Args {
			if err := walkOblig(a, hyps); err != nil {
				return err
			}
		}
		if x.Op == "-" {
			l := obligLin(x.Args[0])
			r := obligLin(x.Args[1])
			if !Decide(Fact{Op: FactGe, L: linAdd(l, r, -1)}, hyps) {
				return fmt.Errorf("cannot prove %s ≥ %s here; nat subtraction needs a guard that establishes it (for example an `if %s == 0` early return)",
					x.Args[0], x.Args[1], x.Args[0])
			}
		}
		return nil
	case Ctor:
		for _, a := range x.Args {
			if err := walkOblig(a, hyps); err != nil {
				return err
			}
		}
		return nil
	case Call:
		for _, a := range x.Args {
			if err := walkOblig(a, hyps); err != nil {
				return err
			}
		}
		return nil
	case If:
		if err := walkOblig(x.L, hyps); err != nil {
			return err
		}
		if err := walkOblig(x.R, hyps); err != nil {
			return err
		}
		l, r := obligLin(x.L), obligLin(x.R)
		if err := walkOblig(x.Then, append(hyps, condFacts(x.Op, l, r)...)); err != nil {
			return err
		}
		return walkOblig(x.Else, append(hyps, condFacts(negateOp(x.Op), l, r)...))
	case MatchT:
		if err := walkOblig(x.Scrut, hyps); err != nil {
			return err
		}
		for _, arm := range x.Arms {
			if err := walkOblig(arm.Body, hyps); err != nil {
				return err
			}
		}
		return nil
	}
	return fmt.Errorf("goplus internal: unknown term %T in obligation check", t)
}

// condFacts converts a comparison into decider hypotheses. != yields a
// usable fact only against 0 (nat: a != 0 means a ≥ 1).
func condFacts(op string, l, r VLin) []Fact {
	ge := func(a, b VLin) Fact { return Fact{Op: FactGe, L: linAdd(a, b, -1)} }
	one := linConst(big.NewInt(1))
	switch op {
	case "==":
		return []Fact{{Op: FactEq, L: linAdd(l, r, -1)}}
	case "!=":
		if ground(r) && r.Const.Sign() == 0 {
			return []Fact{ge(l, one)}
		}
		if ground(l) && l.Const.Sign() == 0 {
			return []Fact{ge(r, one)}
		}
		return nil
	case "<":
		return []Fact{ge(r, linAdd(l, one, 1))}
	case "<=":
		return []Fact{ge(r, l)}
	case ">":
		return []Fact{ge(l, linAdd(r, one, 1))}
	case ">=":
		return []Fact{ge(l, r)}
	}
	return nil
}

func negateOp(op string) string {
	switch op {
	case "==":
		return "!="
	case "!=":
		return "=="
	case "<":
		return ">="
	case "<=":
		return ">"
	case ">":
		return "<="
	case ">=":
		return "<"
	}
	return op
}

// obligLin linearizes a term for obligation checking: +/- combine,
// everything else (variables, calls, products, stuck shapes) atomizes
// by printed form. Every atom is a nat, hence implicitly ≥ 0.
func obligLin(t Term) VLin {
	switch x := t.(type) {
	case Nat:
		return linConst(x.N)
	case Prim:
		switch x.Op {
		case "+", "-":
			out := obligLin(x.Args[0])
			s := int64(1)
			if x.Op == "-" {
				s = -1
			}
			for _, a := range x.Args[1:] {
				out = linAdd(out, obligLin(a), s)
			}
			return out
		}
	}
	return linAtom(VNeu{N: NVar{Name: t.String()}})
}

// IndexClash reports whether a use-site index term and a variant's
// index term can NEVER unify: both normalize symbolically (free
// variables as non-negative nat atoms, unknown calls neutral) and
// either ground constructor tags differ or the difference is a linear
// form with no root.
func IndexClash(useTerm, variantTerm string, tagOf func(string) (string, bool)) bool {
	ct, err1 := ParseIndexTerm(useTerm, permissiveResolver)
	vt, err2 := ParseIndexTerm(variantTerm, permissiveResolver)
	if err1 != nil || err2 != nil {
		return false
	}
	if tagOf != nil {
		ct = ResolveTags(ct, tagOf)
		vt = ResolveTags(vt, tagOf)
	}
	// The variant's binders are its own scope: α-rename them apart so a
	// caller-side variable that happens to share a name never aliases.
	vt = renameFree(vt, "goplus·v·")
	cv, vv := symbolicValue(ct), symbolicValue(vt)
	if cv == nil || vv == nil {
		return false
	}
	if cc, ok1 := cv.(VCtor); ok1 {
		if vc, ok2 := vv.(VCtor); ok2 {
			return cc.Name != vc.Name
		}
		return false
	}
	return LinNeverZero(cv, vv)
}

func permissiveResolver(fun ast.Expr) (string, bool) {
	switch fn := fun.(type) {
	case *ast.Ident:
		return fn.Name, true
	case *ast.SelectorExpr:
		return fn.Sel.Name, true
	}
	return "", false
}

// symbolicValue evaluates a term with every free variable as a nat atom.
func symbolicValue(t Term) Value { return symbolicValueDefs(t, nil) }

// symbolicValueDefs is symbolicValue with total definitions available:
// ground total calls unfold; unknown or stuck calls stay neutral.
func symbolicValueDefs(t Term, defs Defs) Value {
	env := Env{}
	for _, fv := range FreeVars(t) {
		env[fv] = NatVar(fv)
	}
	ev := &Evaluator{Defs: defs, Fuel: 1 << 16, Permissive: true}
	v, err := ev.Eval(t, env)
	if err != nil {
		return nil
	}
	return v
}

// renameFree prefixes every free variable of a term.
func renameFree(t Term, prefix string) Term {
	switch x := t.(type) {
	case Var:
		return Var{Name: prefix + x.Name}
	case Prim:
		args := make([]Term, len(x.Args))
		for i, a := range x.Args {
			args[i] = renameFree(a, prefix)
		}
		return Prim{Op: x.Op, Args: args}
	case Ctor:
		args := make([]Term, len(x.Args))
		for i, a := range x.Args {
			args[i] = renameFree(a, prefix)
		}
		return Ctor{Type: x.Type, Name: x.Name, Args: args}
	case Call:
		args := make([]Term, len(x.Args))
		for i, a := range x.Args {
			args[i] = renameFree(a, prefix)
		}
		return Call{Fn: x.Fn, Args: args}
	}
	return t
}
