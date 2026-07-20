package core

import (
	"fmt"
	"math/big"
	"strings"
)

// Termination checking (v0.7.0): every self-recursive call must shrink
// some argument. Two descent shapes are recognized:
//
//   - structural: the argument is a match binder (transitively) obtained
//     by destructing the corresponding parameter — a strict subterm;
//   - arithmetic: the argument's linear form is param + c with c ≤ -1
//     (the guarded-subtraction shape `a-1`; well-definedness of the
//     subtraction itself is a separate elaboration obligation).
//
// Mutual recursion is not supported in v1: calls to other total
// functions must be to already-checked definitions (dependency order),
// and only self-calls are inspected for descent.

// CheckTotal verifies structural termination of def. callable reports
// whether a non-self callee is a known total function (existence of
// import-qualified callees may be deferred to a later pass by answering
// true; nil admits nothing).
func CheckTotal(def *Def, callable func(string) bool) error {
	c := &totalChecker{def: def, callable: callable}
	// smaller[v] = index of the parameter v strictly descends from.
	smaller := map[string]int{}
	roots := map[string]int{}
	for i, p := range def.Params {
		roots[p] = i
	}
	return c.walk(def.Body, roots, smaller)
}

type totalChecker struct {
	def      *Def
	callable func(string) bool
}

// walk descends the body. roots maps names that ARE a parameter (or an
// alias of one at the same size) to its index; smaller maps names known
// strictly smaller than the parameter at the index.
func (c *totalChecker) walk(t Term, roots, smaller map[string]int) error {
	switch x := t.(type) {
	case Var, Nat:
		return nil
	case Prim:
		for _, a := range x.Args {
			if err := c.walk(a, roots, smaller); err != nil {
				return err
			}
		}
		return nil
	case Ctor:
		for _, a := range x.Args {
			if err := c.walk(a, roots, smaller); err != nil {
				return err
			}
		}
		return nil
	case If:
		for _, s := range []Term{x.L, x.R, x.Then, x.Else} {
			if err := c.walk(s, roots, smaller); err != nil {
				return err
			}
		}
		return nil
	case MatchT:
		if err := c.walk(x.Scrut, roots, smaller); err != nil {
			return err
		}
		// Binders of a match on a parameter (or on something already
		// smaller) are strictly smaller than that parameter.
		var descendsFrom = -1
		if v, ok := x.Scrut.(Var); ok {
			if i, ok := roots[v.Name]; ok {
				descendsFrom = i
			} else if i, ok := smaller[v.Name]; ok {
				descendsFrom = i
			}
		}
		for _, arm := range x.Arms {
			r2, s2 := cloneIdx(roots), cloneIdx(smaller)
			for _, b := range arm.Binds {
				delete(r2, b)
				delete(s2, b)
				if descendsFrom >= 0 {
					s2[b] = descendsFrom
				}
			}
			if err := c.walk(arm.Body, r2, s2); err != nil {
				return err
			}
		}
		return nil
	case Call:
		for _, a := range x.Args {
			if err := c.walk(a, roots, smaller); err != nil {
				return err
			}
		}
		if x.Fn != c.def.Name {
			if c.callable == nil || !c.callable(x.Fn) {
				return fmt.Errorf("total function %s calls %s, which is not a total function (only total functions may be called here; mutual recursion is not yet supported)", ShortName(c.def.Name), ShortName(x.Fn))
			}
			return nil
		}
		if len(x.Args) != len(c.def.Params) {
			return fmt.Errorf("total function %s calls itself with %d arguments, expected %d", ShortName(c.def.Name), len(x.Args), len(c.def.Params))
		}
		for i, a := range x.Args {
			if c.decreases(a, i, roots, smaller) {
				return nil
			}
		}
		return fmt.Errorf("total function %s does not terminate: this recursive call shrinks no argument (destructure a parameter with match, or recurse on p-1 for a nat parameter p)", ShortName(c.def.Name))
	}
	return fmt.Errorf("goplus internal: unknown term %T in termination check", t)
}

// decreases reports whether arg is strictly smaller than parameter i.
func (c *totalChecker) decreases(arg Term, i int, roots, smaller map[string]int) bool {
	// Structural: a binder marked smaller-than-parameter-i.
	if v, ok := arg.(Var); ok {
		if j, ok := smaller[v.Name]; ok && j == i {
			return true
		}
	}
	// Arithmetic: linearize over parameter atoms; accept p_i + c, c ≤ -1.
	l, ok := symbolicLin(arg)
	if !ok {
		return false
	}
	if l.Const.Cmp(big.NewInt(-1)) > 0 {
		return false
	}
	if len(l.Coef) != 1 {
		return false
	}
	p := c.def.Params[i]
	if _, isRoot := roots[p]; !isRoot {
		return false // parameter shadowed on this path
	}
	coef, has := l.Coef[p]
	return has && coef.Cmp(bigOne) == 0
}

// symbolicLin linearizes a term treating variables as atoms, without an
// evaluator (only +, -, literals, and variables; anything else opts the
// shape out of arithmetic descent).
func symbolicLin(t Term) (VLin, bool) {
	switch x := t.(type) {
	case Nat:
		return linConst(x.N), true
	case Var:
		return linAtom(VNeu{N: NVar{Name: x.Name}}), true
	case Prim:
		if x.Op != "+" && x.Op != "-" {
			return VLin{}, false
		}
		out, ok := symbolicLin(x.Args[0])
		if !ok {
			return VLin{}, false
		}
		s := int64(1)
		if x.Op == "-" {
			s = -1
		}
		for _, a := range x.Args[1:] {
			l, ok := symbolicLin(a)
			if !ok {
				return VLin{}, false
			}
			out = linAdd(out, l, s)
		}
		return out, true
	}
	return VLin{}, false
}

// ShortName strips a canonical "pkgpath.Name" key to its bare name for
// user-facing messages.
func ShortName(key string) string {
	if i := strings.LastIndex(key, "."); i >= 0 {
		return key[i+1:]
	}
	return key
}

func cloneIdx(m map[string]int) map[string]int {
	out := make(map[string]int, len(m))
	for k, v := range m {
		out[k] = v
	}
	return out
}
