package core

import (
	"fmt"
	"math/big"
	"sort"
	"strings"
)

// Term is the first-order dependent core: nat arithmetic, constructor
// data (enum tags and structured first-order values), calls to total
// functions, guarded conditionals, and one-level structural match.
// There are no term-level binders except match arms — total functions
// are top-level definitions — which keeps substitution and NbE simple.
type Term interface {
	isTerm()
	String() string
}

// Var references a parameter or match binder.
type Var struct{ Name string }

// Nat is a natural-number literal (arbitrary precision).
type Nat struct{ N *big.Int }

// Prim is built-in nat arithmetic: "+", "*", or guarded "-" (v - k,
// admissible only where the decider proves v ≥ k).
type Prim struct {
	Op   string
	Args []Term
}

// Ctor builds first-order data: an enum tag (no args) or a structured
// value. Type is the defining enum's name.
type Ctor struct {
	Type string
	Name string
	Args []Term
}

// Call invokes a total function.
type Call struct {
	Fn   string
	Args []Term
}

// If branches on a nat comparison: Op one of == != < <= > >=.
type If struct {
	Op         string
	L, R       Term
	Then, Else Term
}

// MatchT branches on first-order data one level deep. Arms are keyed by
// constructor name; a nil Body map entry is absent coverage (checked by
// the elaborator, not here).
type MatchT struct {
	Scrut Term
	Arms  []MatchArm
}

// MatchArm is one constructor case with its field binders.
type MatchArm struct {
	Ctor  string
	Binds []string
	Body  Term
}

func (Var) isTerm()    {}
func (Nat) isTerm()    {}
func (Prim) isTerm()   {}
func (Ctor) isTerm()   {}
func (Call) isTerm()   {}
func (If) isTerm()     {}
func (MatchT) isTerm() {}

func (t Var) String() string { return t.Name }
func (t Nat) String() string { return t.N.String() }
func (t Prim) String() string {
	parts := make([]string, len(t.Args))
	for i, a := range t.Args {
		parts[i] = a.String()
	}
	return "(" + strings.Join(parts, " "+t.Op+" ") + ")"
}
func (t Ctor) String() string {
	if len(t.Args) == 0 {
		return t.Name
	}
	parts := make([]string, len(t.Args))
	for i, a := range t.Args {
		parts[i] = a.String()
	}
	return t.Name + "(" + strings.Join(parts, ", ") + ")"
}
func (t Call) String() string {
	parts := make([]string, len(t.Args))
	for i, a := range t.Args {
		parts[i] = a.String()
	}
	return t.Fn + "(" + strings.Join(parts, ", ") + ")"
}
func (t If) String() string {
	return fmt.Sprintf("if %s %s %s then %s else %s", t.L, t.Op, t.R, t.Then, t.Else)
}
func (t MatchT) String() string {
	var b strings.Builder
	fmt.Fprintf(&b, "match %s {", t.Scrut)
	for i, a := range t.Arms {
		if i > 0 {
			b.WriteString("; ")
		}
		fmt.Fprintf(&b, "%s(%s) => %s", a.Ctor, strings.Join(a.Binds, ", "), a.Body)
	}
	b.WriteString("}")
	return b.String()
}

// Def is one total function definition.
type Def struct {
	Name   string
	Params []string
	Body   Term
}

// Defs is the definition environment (total functions by name).
type Defs map[string]*Def

// DataDef describes one first-order index data type (an enum usable as
// an index domain): constructor name -> arity.
type DataDef struct {
	Name  string
	Ctors map[string]int
}

// FreeVars returns the free variables of t in sorted order.
func FreeVars(t Term) []string {
	seen := map[string]bool{}
	var walk func(t Term, bound map[string]bool)
	walk = func(t Term, bound map[string]bool) {
		switch x := t.(type) {
		case Var:
			if !bound[x.Name] {
				seen[x.Name] = true
			}
		case Prim:
			for _, a := range x.Args {
				walk(a, bound)
			}
		case Ctor:
			for _, a := range x.Args {
				walk(a, bound)
			}
		case Call:
			for _, a := range x.Args {
				walk(a, bound)
			}
		case If:
			walk(x.L, bound)
			walk(x.R, bound)
			walk(x.Then, bound)
			walk(x.Else, bound)
		case MatchT:
			walk(x.Scrut, bound)
			for _, arm := range x.Arms {
				inner := map[string]bool{}
				for k := range bound {
					inner[k] = true
				}
				for _, b := range arm.Binds {
					inner[b] = true
				}
				walk(arm.Body, inner)
			}
		}
	}
	walk(t, map[string]bool{})
	out := make([]string, 0, len(seen))
	for k := range seen {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

// ResolveTags rewrites free variables that name enum tags into
// constructor terms (index elaboration sees `Open` as an identifier;
// the enum's tag table disambiguates it from a binder).
func ResolveTags(t Term, tagOf func(name string) (enum string, ok bool)) Term {
	switch x := t.(type) {
	case Var:
		if enum, ok := tagOf(x.Name); ok {
			return Ctor{Type: enum, Name: x.Name}
		}
		return x
	case Prim:
		args := make([]Term, len(x.Args))
		for i, a := range x.Args {
			args[i] = ResolveTags(a, tagOf)
		}
		return Prim{Op: x.Op, Args: args}
	case Ctor:
		args := make([]Term, len(x.Args))
		for i, a := range x.Args {
			args[i] = ResolveTags(a, tagOf)
		}
		return Ctor{Type: x.Type, Name: x.Name, Args: args}
	case Call:
		args := make([]Term, len(x.Args))
		for i, a := range x.Args {
			args[i] = ResolveTags(a, tagOf)
		}
		// A structured tag (`Circle(3)`) elaborates as a call; the tag
		// table turns it back into a constructor.
		if enum, ok := tagOf(ShortName(x.Fn)); ok {
			return Ctor{Type: enum, Name: ShortName(x.Fn), Args: args}
		}
		return Call{Fn: x.Fn, Args: args}
	case If:
		return If{Op: x.Op, L: ResolveTags(x.L, tagOf), R: ResolveTags(x.R, tagOf),
			Then: ResolveTags(x.Then, tagOf), Else: ResolveTags(x.Else, tagOf)}
	case MatchT:
		arms := make([]MatchArm, len(x.Arms))
		for i, a := range x.Arms {
			arms[i] = MatchArm{Ctor: a.Ctor, Binds: a.Binds, Body: ResolveTags(a.Body, tagOf)}
		}
		return MatchT{Scrut: ResolveTags(x.Scrut, tagOf), Arms: arms}
	}
	return t
}

// SubstVars replaces free variables by terms (capture-safe: the core's
// only binders are match arms, whose binds shadow).
func SubstVars(t Term, sub map[string]Term) Term {
	switch x := t.(type) {
	case Var:
		if r, ok := sub[x.Name]; ok {
			return r
		}
		return x
	case Prim:
		args := make([]Term, len(x.Args))
		for i, a := range x.Args {
			args[i] = SubstVars(a, sub)
		}
		return Prim{Op: x.Op, Args: args}
	case Ctor:
		args := make([]Term, len(x.Args))
		for i, a := range x.Args {
			args[i] = SubstVars(a, sub)
		}
		return Ctor{Type: x.Type, Name: x.Name, Args: args}
	case Call:
		args := make([]Term, len(x.Args))
		for i, a := range x.Args {
			args[i] = SubstVars(a, sub)
		}
		return Call{Fn: x.Fn, Args: args}
	case If:
		return If{Op: x.Op, L: SubstVars(x.L, sub), R: SubstVars(x.R, sub),
			Then: SubstVars(x.Then, sub), Else: SubstVars(x.Else, sub)}
	}
	return t
}

// DecideEqTexts parses two index terms, substitutes caller argument
// terms for callee parameter names, and asks the decider whether the
// equality holds symbolically (free variables as non-negative nats).
func DecideEqTexts(aText, bText string, sub map[string]Term) (bool, error) {
	a, err := ParseIndexTerm(aText, permissiveResolver)
	if err != nil {
		return false, err
	}
	b, err := ParseIndexTerm(bText, permissiveResolver)
	if err != nil {
		return false, err
	}
	a, b = SubstVars(a, sub), SubstVars(b, sub)
	av, bv := symbolicValue(a), symbolicValue(b)
	if av == nil || bv == nil {
		return false, nil
	}
	return Decide(MkEq(av, bv), nil), nil
}
