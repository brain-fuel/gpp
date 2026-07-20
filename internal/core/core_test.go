package core

import (
	"math/big"
	"strings"
	"testing"
)

func nat(n int64) Term     { return Nat{N: big.NewInt(n)} }
func v(name string) Term   { return Var{Name: name} }
func plus(a, b Term) Term  { return Prim{Op: "+", Args: []Term{a, b}} }
func minus(a, b Term) Term { return Prim{Op: "-", Args: []Term{a, b}} }
func times(a, b Term) Term { return Prim{Op: "*", Args: []Term{a, b}} }

// plusDef is the canonical guarded-recursion definition:
//
//	total func Plus(a, b nat) nat {
//		if a == 0 { return b }
//		return Plus(a-1, b) + 1
//	}
func plusDef() *Def {
	return &Def{
		Name:   "Plus",
		Params: []string{"a", "b"},
		Body: If{
			Op: "==", L: v("a"), R: nat(0),
			Then: v("b"),
			Else: plus(Call{Fn: "Plus", Args: []Term{minus(v("a"), nat(1)), v("b")}}, nat(1)),
		},
	}
}

func mustEval(t *testing.T, defs Defs, term Term, env Env) Value {
	t.Helper()
	val, err := NewEvaluator(defs).Eval(term, env)
	if err != nil {
		t.Fatalf("eval %s: %v", term, err)
	}
	return val
}

func TestGroundArithmetic(t *testing.T) {
	got := mustEval(t, nil, plus(nat(2), times(nat(3), nat(4))), Env{})
	if got.String() != "14" {
		t.Fatalf("2+3*4 = %s", got)
	}
}

func TestCanonicalCommutativity(t *testing.T) {
	env := Env{"n": NatVar("n"), "m": NatVar("m")}
	a := mustEval(t, nil, plus(v("n"), v("m")), env)
	b := mustEval(t, nil, plus(v("m"), v("n")), env)
	if !Equal(a, b) {
		t.Fatalf("n+m ≠ m+n: %s vs %s", a, b)
	}
}

func TestDistributionOverGround(t *testing.T) {
	env := Env{"n": NatVar("n")}
	a := mustEval(t, nil, times(nat(2), plus(v("n"), nat(3))), env)
	b := mustEval(t, nil, plus(plus(v("n"), v("n")), nat(6)), env)
	if !Equal(a, b) {
		t.Fatalf("2*(n+3) ≠ n+n+6: %s vs %s", a, b)
	}
}

func TestNonlinearAtomizes(t *testing.T) {
	env := Env{"n": NatVar("n"), "m": NatVar("m")}
	a := mustEval(t, nil, times(v("n"), v("m")), env)
	b := mustEval(t, nil, times(v("m"), v("n")), env)
	if !Equal(a, b) {
		t.Fatalf("n*m ≠ m*n: %s vs %s", a, b)
	}
	if !strings.Contains(a.String(), "*") {
		t.Fatalf("product did not atomize: %s", a)
	}
}

func TestTotalCallUnfoldsGround(t *testing.T) {
	defs := Defs{"Plus": plusDef()}
	got := mustEval(t, defs, Call{Fn: "Plus", Args: []Term{nat(2), nat(3)}}, Env{})
	if got.String() != "5" {
		t.Fatalf("Plus(2,3) = %s", got)
	}
}

func TestTotalCallSticksOnNeutral(t *testing.T) {
	defs := Defs{"Plus": plusDef()}
	env := Env{"n": NatVar("n")}
	got := mustEval(t, defs, Call{Fn: "Plus", Args: []Term{v("n"), nat(3)}}, env)
	if got.String() != "Plus(n, 3)" {
		t.Fatalf("Plus(n,3) normal form: %s", got)
	}
	// Stuck calls still normalize their arguments.
	got2 := mustEval(t, defs, Call{Fn: "Plus", Args: []Term{v("n"), plus(nat(1), nat(2))}}, env)
	if !Equal(got, got2) {
		t.Fatalf("Plus(n,3) ≠ Plus(n,1+2): %s vs %s", got, got2)
	}
}

func TestPartialUnfoldOnGroundHead(t *testing.T) {
	// Plus(2, m): the decreasing argument is ground, so the definition
	// unfolds twice and leaves m+2.
	defs := Defs{"Plus": plusDef()}
	env := Env{"m": NatVar("m")}
	got := mustEval(t, defs, Call{Fn: "Plus", Args: []Term{nat(2), v("m")}}, env)
	want := mustEval(t, nil, plus(v("m"), nat(2)), env)
	if !Equal(got, want) {
		t.Fatalf("Plus(2,m) = %s, want %s", got, want)
	}
}

func TestMatchEval(t *testing.T) {
	// match Cons(h, t) { Nil() => 0; Cons(x, xs) => x }
	scrut := Ctor{Type: "List", Name: "Cons", Args: []Term{nat(7), Ctor{Type: "List", Name: "Nil"}}}
	m := MatchT{Scrut: scrut, Arms: []MatchArm{
		{Ctor: "Nil", Body: nat(0)},
		{Ctor: "Cons", Binds: []string{"x", "xs"}, Body: v("x")},
	}}
	got := mustEval(t, nil, m, Env{})
	if got.String() != "7" {
		t.Fatalf("match = %s", got)
	}
}

func TestStuckMatchesDifferingBodiesUnequal(t *testing.T) {
	env := Env{"s": DataVar("s")}
	mk := func(body Term) Value {
		return mustEval(t, nil, MatchT{Scrut: v("s"), Arms: []MatchArm{
			{Ctor: "Nil", Body: body},
		}}, env)
	}
	if Equal(mk(nat(0)), mk(nat(1))) {
		t.Fatal("stuck matches with different bodies compared equal")
	}
}

func TestDecideEqFromHypothesis(t *testing.T) {
	n, m, p := NatVar("n"), NatVar("m"), NatVar("p")
	one := NatConst(1)
	// n = m+1 ⊢ n+p = m+p+1
	hyp := MkEq(n, asAdd(m, one))
	goal := MkEq(asAdd(n, p), asAdd(asAdd(m, p), one))
	if !Decide(goal, []Fact{hyp}) {
		t.Fatal("n=m+1 ⊬ n+p = m+p+1")
	}
}

func TestDecideGeFromHypothesis(t *testing.T) {
	n, m := NatVar("n"), NatVar("m")
	one := NatConst(1)
	// n = m+1 ⊢ n ≥ 1
	if !Decide(MkGe(n, one), []Fact{MkEq(n, asAdd(m, one))}) {
		t.Fatal("n=m+1 ⊬ n ≥ 1")
	}
	// no hypotheses: n ≥ 0 (atoms are nats)
	if !Decide(MkGe(n, NatConst(0)), nil) {
		t.Fatal("⊬ n ≥ 0")
	}
}

func TestDecideRefusesNonFacts(t *testing.T) {
	n, m := NatVar("n"), NatVar("m")
	if Decide(MkEq(n, m), nil) {
		t.Fatal("⊢ n = m accepted with no hypotheses")
	}
	if Decide(MkGe(n, NatConst(1)), nil) {
		t.Fatal("⊢ n ≥ 1 accepted with no hypotheses")
	}
}

func TestDecideContradictionEntailsAnything(t *testing.T) {
	n := NatVar("n")
	// n = 0 and n = 1 ⊢ anything
	hyps := []Fact{MkEq(n, NatConst(0)), MkEq(n, NatConst(1))}
	if !Decide(MkEq(NatConst(3), NatConst(4)), hyps) {
		t.Fatal("contradictory hypotheses did not entail")
	}
}

func TestDecideChainedInequalities(t *testing.T) {
	i, n, m := NatVar("i"), NatVar("n"), NatVar("m")
	one := NatConst(1)
	// i+1 ≤ n, n ≤ m ⊢ i+1 ≤ m
	hyps := []Fact{MkGe(n, asAdd(i, one)), MkGe(m, n)}
	if !Decide(MkGe(m, asAdd(i, one)), hyps) {
		t.Fatal("i+1≤n, n≤m ⊬ i+1 ≤ m")
	}
}

func TestCheckTotalAcceptsPlus(t *testing.T) {
	if err := CheckTotal(plusDef(), nil); err != nil {
		t.Fatalf("Plus rejected: %v", err)
	}
}

func TestCheckTotalAcceptsStructural(t *testing.T) {
	// total func Len(l List) nat { match l { Nil => 0; Cons(h, t) => Len(t)+1 } }
	def := &Def{
		Name:   "Len",
		Params: []string{"l"},
		Body: MatchT{Scrut: v("l"), Arms: []MatchArm{
			{Ctor: "Nil", Body: nat(0)},
			{Ctor: "Cons", Binds: []string{"h", "t"}, Body: plus(Call{Fn: "Len", Args: []Term{v("t")}}, nat(1))},
		}},
	}
	if err := CheckTotal(def, nil); err != nil {
		t.Fatalf("Len rejected: %v", err)
	}
}

func TestCheckTotalRejectsNonDecreasing(t *testing.T) {
	// total func Bad(a nat) nat { return Bad(a+1) }
	def := &Def{
		Name:   "Bad",
		Params: []string{"a"},
		Body:   Call{Fn: "Bad", Args: []Term{plus(v("a"), nat(1))}},
	}
	err := CheckTotal(def, nil)
	if err == nil || !strings.Contains(err.Error(), "shrinks no argument") {
		t.Fatalf("Bad accepted or wrong error: %v", err)
	}
}

func TestCheckTotalRejectsSameArg(t *testing.T) {
	def := &Def{
		Name:   "Loop",
		Params: []string{"a", "b"},
		Body:   Call{Fn: "Loop", Args: []Term{v("a"), v("b")}},
	}
	if err := CheckTotal(def, nil); err == nil {
		t.Fatal("Loop(a,b)=Loop(a,b) accepted")
	}
}

func TestCheckTotalRejectsUnknownCallee(t *testing.T) {
	def := &Def{
		Name:   "F",
		Params: []string{"a"},
		Body:   Call{Fn: "Mystery", Args: []Term{v("a")}},
	}
	err := CheckTotal(def, nil)
	if err == nil || !strings.Contains(err.Error(), "mutual recursion") {
		t.Fatalf("unknown callee accepted or wrong error: %v", err)
	}
}

func TestQuantitySemiring(t *testing.T) {
	q0, q1, w := Quantity{K: Q0}, Quantity{K: Q1}, Quantity{K: QOmega}
	if Add(q1, q1).K != QOmega {
		t.Fatal("1+1 ≠ ω")
	}
	if Add(q0, q1).K != Q1 {
		t.Fatal("0+1 ≠ 1")
	}
	if Mul(q0, w).K != Q0 {
		t.Fatal("0·ω ≠ 0")
	}
	if Mul(q1, q1).K != Q1 {
		t.Fatal("1·1 ≠ 1")
	}
	if !LeqUsage(q0, Quantity{K: QVar, Var: "m"}) {
		t.Fatal("0 not admissible at m")
	}
	if LeqUsage(w, q1) {
		t.Fatal("ω admissible at 1")
	}
}

// asAdd adds two nat VALUES (test convenience over the evaluator).
func asAdd(a, b Value) Value { return linAdd(asLin(a), asLin(b), 1) }
