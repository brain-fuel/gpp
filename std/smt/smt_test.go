package smt

import (
	"goforge.dev/goplus/std/vec"
	"math/big"
	"math/rand"
	"sync"
	"sync/atomic"
	"testing"
)

func ternaryDatatypeNames() vec.Vec[string] {
	return vec.Cons[string]{Head: "first", Tail: vec.Cons[string]{Head: "second", Tail: vec.Cons[string]{Head: "third", Tail: vec.Nil[string]{}}}}
}

func ternaryDatatypeValues(first, second, third Term[DatatypeSort]) vec.Vec[Term[DatatypeSort]] {
	return vec.Cons[Term[DatatypeSort]]{Head: first, Tail: vec.Cons[Term[DatatypeSort]]{Head: second, Tail: vec.Cons[Term[DatatypeSort]]{Head: third, Tail: vec.Nil[Term[DatatypeSort]]{}}}}
}

func TestBooleanSatModel(t *testing.T) {
	a := BoolSymbol{ID: 1, Name: "a"}
	b := BoolSymbol{ID: 2, Name: "b"}
	formula := And{Values: []Term[BoolSort]{Or{Values: []Term[BoolSort]{a, b}}, Not{Value: a}}}
	solver := Assert(1, New(), formula)
	result, ok := Check(solver).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(solver))
	}
	if value, found := BoolValue(result.Value, a); !found || value {
		t.Fatalf("a=(%v,%v)", value, found)
	}
	if value, found := BoolValue(result.Value, b); !found || !value {
		t.Fatalf("b=(%v,%v)", value, found)
	}
}

func TestBooleanUnsatProof(t *testing.T) {
	a := BoolSymbol{ID: 1, Name: "a"}
	formula := And{Values: []Term[BoolSort]{a, Not{Value: a}}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("expected unsatisfiable")
	}
}

func TestBooleanInlineCNFModelAndContradiction(t *testing.T) {
	satisfiable := BooleanInlineCNF{LiteralCount: 3, ClauseCount: 2}
	satisfiable.Literals[0], satisfiable.Literals[1], satisfiable.Literals[2] = 1, 2, -1
	satisfiable.ClauseEnds[0], satisfiable.ClauseEnds[1] = 2, 3
	result, ok := Check(Assert(1, New(), satisfiable)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, New(), satisfiable)))
	}
	if value, found := BoolValue(result.Value, BoolSymbol{ID: 0}); !found || value {
		t.Fatalf("a=(%v,%v)", value, found)
	}
	if value, found := BoolValue(result.Value, BoolSymbol{ID: 1}); !found || !value {
		t.Fatalf("b=(%v,%v)", value, found)
	}

	unsatisfiable := BooleanInlineCNF{LiteralCount: 2, ClauseCount: 2}
	unsatisfiable.Literals[0], unsatisfiable.Literals[1] = 1, -1
	unsatisfiable.ClauseEnds[0], unsatisfiable.ClauseEnds[1] = 1, 2
	if _, ok := Check(Assert(2, New(), unsatisfiable)).(Unsatisfiable); !ok {
		t.Fatal("expected inline contradiction to be unsatisfiable")
	}
}

func TestBooleanChoiceCNFSparseModelAndContradiction(t *testing.T) {
	satisfiable := BooleanCNF{
		Literals:   []int{2, 3, 5, 6, -2, -5, -3, -6},
		ClauseEnds: []int{2, 4, 6, 8},
	}
	result, ok := Check(Assert(1, New(), satisfiable)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, New(), satisfiable)))
	}
	if value, complete := BoolValue(result.Value, satisfiable); !complete || !value {
		t.Fatalf("choice model=(%v,%v)", value, complete)
	}

	unsatisfiable := BooleanCNF{
		Literals:   []int{2, 5, -2, -5},
		ClauseEnds: []int{1, 2, 4},
	}
	if _, ok := Check(Assert(2, New(), unsatisfiable)).(Unsatisfiable); !ok {
		t.Fatal("expected incompatible singleton choices to be unsatisfiable")
	}
}

func TestLinearIntegerArithmeticSatModel(t *testing.T) {
	x := IntSymbol{ID: 1, Name: "x"}
	y := IntSymbol{ID: 2, Name: "y"}
	formula := And{Values: []Term[BoolSort]{
		LessEqual{Left: Add{Values: []Term[IntSort]{x, y}}, Right: Integer{Value: 10}},
		LessEqual{Left: Integer{Value: 11}, Right: Add{Values: []Term[IntSort]{ScaleInteger(NewIntegerValue(2), x), y}}},
	}}
	checked := Check(Assert(1, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T (%#v)", checked, checked)
	}
	xValue, xOK := IntegerModelValue(result.Value, x)
	yValue, yOK := IntegerModelValue(result.Value, y)
	if !xOK || !yOK {
		t.Fatalf("model x=(%v,%v) y=(%v,%v)", xValue, xOK, yValue, yOK)
	}
	if CompareIntegerValue(AddIntegerValue(xValue, yValue), NewIntegerValue(10)) > 0 || CompareIntegerValue(AddIntegerValue(MultiplyIntegerValue(NewIntegerValue(2), xValue), yValue), NewIntegerValue(11)) < 0 {
		t.Fatalf("invalid model x=%v y=%v", xValue, yValue)
	}
}

func TestLinearIntegerArithmeticIntegralityUnsat(t *testing.T) {
	x := IntSymbol{ID: 1, Name: "x"}
	twoX := ScaleInteger(NewIntegerValue(2), x)
	formula := Equal{Left: twoX, Right: Integer{Value: 1}}
	result := Check(Assert(1, New(), formula))
	if _, ok := result.(Unsatisfiable); !ok {
		t.Fatalf("result=%T", result)
	}
}

func TestLinearIntegerArithmeticCoefficientOverflow(t *testing.T) {
	variables := make([]Term[IntSort], 6)
	terms := make([]Term[IntSort], 6)
	for index := range variables {
		variables[index] = IntSymbol{ID: index + 1}
		terms[index] = ScaleInteger(NewIntegerValue(int64(index+1)), variables[index])
	}
	formula := Equal{Left: Add{Values: terms}, Right: Integer{Value: 21}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	total := IntegerValue{}
	for index, variable := range variables {
		value, found := IntegerModelValue(result.Value, variable)
		if !found {
			t.Fatalf("missing variable %d", index+1)
		}
		total = AddIntegerValue(total, MultiplyIntegerValue(NewIntegerValue(int64(index+1)), value))
	}
	if CompareIntegerValue(total, NewIntegerValue(21)) != 0 {
		t.Fatalf("invalid weighted sum %v", total)
	}
}

func TestBooleanLinearIntegerArithmetic(t *testing.T) {
	x := IntSymbol{ID: 1, Name: "x"}
	zero := Equal{Left: x, Right: Integer{Value: 0}}
	two := Equal{Left: x, Right: Integer{Value: 2}}
	formula := And{Values: []Term[BoolSort]{Or{Values: []Term[BoolSort]{zero, two}}, Not{Value: zero}}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	value, found := IntegerModelValue(result.Value, x)
	if !found || CompareIntegerValue(value, NewIntegerValue(2)) != 0 {
		t.Fatalf("x=(%v,%v)", value, found)
	}

	contradiction := And{Values: []Term[BoolSort]{zero, Implies{Left: zero, Right: two}}}
	implicationResult := Check(Assert(2, New(), contradiction))
	if _, ok := implicationResult.(Unsatisfiable); !ok {
		t.Fatalf("implication result=%T", implicationResult)
	}
}

func TestBooleanLinearIntegerBranchLimitIsExplicit(t *testing.T) {
	x := IntSymbol{ID: 1, Name: "x"}
	terms := make([]Term[BoolSort], 9)
	for index := range terms {
		terms[index] = Not{Value: Equal{Left: x, Right: Integer{Value: int64(index)}}}
	}
	result, ok := Check(Assert(1, New(), And{Values: terms})).(Unknown)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	if limit, ok := result.Reason.(ResourceLimit); !ok || limit.Limit != linearIntegerBooleanBranchLimit {
		t.Fatalf("reason=%#v", result.Reason)
	}
}

func TestIntegerEuclideanDivisionAndModulo(t *testing.T) {
	for _, test := range []struct {
		dividend, divisor   int64
		quotient, remainder int64
	}{
		{7, 3, 2, 1},
		{-1, 3, -1, 2},
		{-7, 3, -3, 2},
		{7, -3, -2, 1},
		{-1, -3, 1, 2},
		{-7, -3, 3, 2},
		{1, -3, 0, 1},
	} {
		quotient, remainder, ok := DivModIntegerValue(NewIntegerValue(test.dividend), NewIntegerValue(test.divisor))
		if !ok || CompareIntegerValue(quotient, NewIntegerValue(test.quotient)) != 0 || CompareIntegerValue(remainder, NewIntegerValue(test.remainder)) != 0 {
			t.Fatalf("%d divmod %d = (%v,%v,%v)", test.dividend, test.divisor, quotient, remainder, ok)
		}
	}
	if _, _, ok := DivModIntegerValue(NewIntegerValue(7), IntegerValue{}); ok {
		t.Fatal("zero divisor must not have a defined value")
	}
	minimumQuotient, minimumRemainder, ok := DivModIntegerValue(NewIntegerValue(-1<<63), NewIntegerValue(-1))
	wantMinimumQuotient, err := ParseIntegerValue("9223372036854775808")
	if err != nil || !ok || CompareIntegerValue(minimumQuotient, wantMinimumQuotient) != 0 || CompareIntegerValue(minimumRemainder, IntegerValue{}) != 0 {
		t.Fatalf("MinInt64 divmod -1 = (%v,%v,%v), parse=%v", minimumQuotient, minimumRemainder, ok, err)
	}

	x := IntSymbol{ID: 1, Name: "x"}
	div := DivInteger(x, NewIntegerValue(3))
	mod := ModInteger(x, NewIntegerValue(3))
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: Integer{Value: -1}},
		Equal{Left: div, Right: Integer{Value: -1}},
		Equal{Left: mod, Right: Integer{Value: 2}},
	}}
	checked := Check(Assert(1, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T (%#v)", checked, checked)
	}
	if value, found := IntegerModelValue(result.Value, div); !found || CompareIntegerValue(value, NewIntegerValue(-1)) != 0 {
		t.Fatalf("div=(%v,%v)", value, found)
	}
	if value, found := IntegerModelValue(result.Value, mod); !found || CompareIntegerValue(value, NewIntegerValue(2)) != 0 {
		t.Fatalf("mod=(%v,%v)", value, found)
	}

	unassigned := And{Values: []Term[BoolSort]{
		LessEqual{Left: Integer{Value: -2}, Right: x},
		LessEqual{Left: x, Right: Integer{Value: 2}},
		Equal{Left: ModInteger(x, NewIntegerValue(3)), Right: Integer{Value: 2}},
	}}
	unassignedResult, ok := Check(Assert(2, New(), unassigned)).(Satisfiable)
	if !ok {
		t.Fatalf("unassigned result=%T", unassignedResult)
	}
	xValue, found := IntegerModelValue(unassignedResult.Value, x)
	if !found {
		t.Fatal("unassigned model omitted x")
	}
	_, remainder, valid := DivModIntegerValue(xValue, NewIntegerValue(3))
	if !valid || CompareIntegerValue(remainder, NewIntegerValue(2)) != 0 {
		t.Fatalf("unassigned x=%v remainder=%v", xValue, remainder)
	}

	negativeDivisor := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: Integer{Value: -7}},
		Equal{Left: DivInteger(x, NewIntegerValue(-3)), Right: Integer{Value: 3}},
		Equal{Left: ModInteger(x, NewIntegerValue(-3)), Right: Integer{Value: 2}},
	}}
	negativeResult, ok := Check(Assert(3, New(), negativeDivisor)).(Satisfiable)
	if !ok {
		t.Fatalf("negative-divisor result=%T", negativeResult)
	}
	if value, found := IntegerModelValue(negativeResult.Value, DivInteger(x, NewIntegerValue(-3))); !found || CompareIntegerValue(value, NewIntegerValue(3)) != 0 {
		t.Fatalf("negative div=(%v,%v)", value, found)
	}

	scaled := ScaleInteger(NewIntegerValue(3), x)
	assignment, assignmentOK := CompactIntegerLinearEquality(x, Integer{Value: 7})
	quotientRelation, quotientOK := CompactIntegerDivModEquality(
		DivInteger(scaled, NewIntegerValue(2)),
		Integer{Value: 10},
	)
	remainderRelation, remainderOK := CompactIntegerDivModEquality(
		ModInteger(scaled, NewIntegerValue(2)),
		Integer{Value: 0},
	)
	remainderRelation.Negated = true
	if !assignmentOK || !quotientOK || !remainderOK ||
		CompareIntegerValue(quotientRelation.DividendCoefficient, NewIntegerValue(3)) != 0 {
		t.Fatal("scaled div/mod relations did not compact")
	}
	scaledSystem := IntegerDivModSystem{
		EqualityCount: 1,
		RelationCount: 2,
		Equalities:    [4]IntegerLinearEquality{assignment},
		Relations:     [4]IntegerDivModRelation{quotientRelation, remainderRelation},
	}
	scaledResult, ok := Check(Assert(4, New(), scaledSystem)).(Satisfiable)
	if !ok {
		t.Fatalf("scaled div/mod result=%T", scaledResult)
	}
	if value, found := IntegerModelValue(scaledResult.Value, x); !found || CompareIntegerValue(value, NewIntegerValue(7)) != 0 {
		t.Fatalf("scaled div/mod x=(%v,%v)", value, found)
	}
}

func TestIntegerDifferenceLogicSatModel(t *testing.T) {
	x := IntSymbol{ID: 1, Name: "x"}
	y := IntSymbol{ID: 2, Name: "y"}
	formula := And{Values: []Term[BoolSort]{
		LessEqual{Left: Subtract{Left: x, Right: y}, Right: Integer{Value: 3}},
		LessEqual{Left: y, Right: Integer{Value: 2}},
		LessEqual{Left: Integer{Value: 4}, Right: x},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	xValue, xFound := IntValue(result.Value, x)
	yValue, yFound := IntValue(result.Value, y)
	if !xFound || !yFound || xValue-yValue > 3 || yValue > 2 || xValue < 4 {
		t.Fatalf("model x=%d/%v y=%d/%v", xValue, xFound, yValue, yFound)
	}
}

func TestIntegerDifferenceLogicNegativeCycle(t *testing.T) {
	x := IntSymbol{ID: -1, Name: "x"}
	y := IntSymbol{ID: 0, Name: "y"}
	formula := And{Values: []Term[BoolSort]{
		LessEqual{Left: Subtract{Left: x, Right: y}, Right: Integer{Value: -1}},
		LessEqual{Left: Subtract{Left: y, Right: x}, Right: Integer{Value: -1}},
	}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("negative cycle should be unsatisfiable")
	}
}

func TestArbitraryPrecisionIntegerDifferenceModel(t *testing.T) {
	lower, err := ParseIntegerValue("1267650600228229401496703205376")
	if err != nil {
		t.Fatal(err)
	}
	upper := AddIntegerValue(lower, NewIntegerValue(1))
	x := IntSymbol{ID: 91, Name: "wide"}
	formula := And{Values: []Term[BoolSort]{
		LessEqual{Left: IntegerTerm(lower), Right: x},
		LessEqual{Left: x, Right: IntegerTerm(upper)},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		checked := Check(Assert(1, New(), formula))
		if unknown, unknownOK := checked.(Unknown); unknownOK {
			t.Fatalf("result=%T reason=%#v", checked, unknown.Reason)
		}
		t.Fatalf("result=%#v", checked)
	}
	value, found := ExactIntValue(result.Value, x)
	if !found || CompareIntegerValue(value, lower) < 0 || CompareIntegerValue(value, upper) > 0 {
		t.Fatalf("wide model=%s/%v", value.String(), found)
	}
	if _, fits := IntValue(result.Value, x); fits {
		t.Fatal("legacy int64 projection must reject a wide model value")
	}
}

func TestArbitraryPrecisionIntegerDifferenceUnsat(t *testing.T) {
	wide, err := ParseIntegerValue("1267650600228229401496703205376")
	if err != nil {
		t.Fatal(err)
	}
	x := IntSymbol{ID: 92, Name: "x"}
	y := IntSymbol{ID: 93, Name: "y"}
	formula := And{Values: []Term[BoolSort]{
		LessEqual{Left: Subtract{Left: x, Right: y}, Right: IntegerTerm(wide)},
		Less{Left: Add{Values: []Term[IntSort]{y, IntegerTerm(wide)}}, Right: x},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestIntegerDifferenceLogicStrictSelfComparison(t *testing.T) {
	x := IntSymbol{ID: 1, Name: "x"}
	if _, ok := Check(Assert(1, New(), Less{Left: x, Right: x})).(Unsatisfiable); !ok {
		t.Fatal("x < x should be unsatisfiable")
	}
}

func TestCheckpointRestoresParent(t *testing.T) {
	a := BoolSymbol{ID: 1, Name: "a"}
	parent := Assert(1, New(), a)
	pushed := Push(parent)
	child := Assert(2, Current(pushed), Not{Value: a})
	if _, ok := Check(child).(Unsatisfiable); !ok {
		t.Fatal("child should be unsatisfiable")
	}
	restored := Restore(child, Previous(pushed))
	if _, ok := Check(restored).(Satisfiable); !ok {
		t.Fatal("restored parent should be satisfiable")
	}
}

func TestCheckAssumingReturnsMinimalCore(t *testing.T) {
	a := BoolSymbol{ID: 1, Name: "a"}
	b := BoolSymbol{ID: 2, Name: "b"}
	solver := Assert(1, New(), Or{Values: []Term[BoolSort]{a, b}})
	result, ok := CheckAssuming(solver, Not{Value: a}, Not{Value: b}, Bool{Value: true}).(AssumptionsUnsatisfiable)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	if len(result.Indices) != 2 || result.Indices[0] != 0 || result.Indices[1] != 1 {
		t.Fatalf("core=%v", result.Indices)
	}
}

func TestCheckAssumingDoesNotMutateSolver(t *testing.T) {
	a := BoolSymbol{ID: 1, Name: "a"}
	solver := Assert(1, New(), a)
	if _, ok := CheckAssuming(solver, Not{Value: a}).(AssumptionsUnsatisfiable); !ok {
		t.Fatal("expected assumption conflict")
	}
	if _, ok := Check(solver).(Satisfiable); !ok {
		t.Fatal("temporary assumption mutated solver")
	}
}

func TestSortedEquality(t *testing.T) {
	a := BoolSymbol{ID: 1, Name: "a"}
	equality := Equal{Left: Term[BoolSort](a), Right: Term[BoolSort](Bool{Value: true})}
	if _, ok := Check(Assert(1, New(), equality)).(Satisfiable); !ok {
		t.Fatal("expected equality to be satisfiable")
	}
}

func TestBooleanCoreHasNoWordSizeVariableLimit(t *testing.T) {
	values := make([]Term[BoolSort], 70)
	for id := range values {
		values[id] = Iff{
			Left:  BoolSymbol{ID: id, Name: "value"},
			Right: Bool{Value: id%2 == 0},
		}
	}
	result, ok := Check(Assert(1, New(), And{Values: values})).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	for id := range values {
		value, found := BoolValue(result.Value, BoolSymbol{ID: id, Name: "value"})
		if !found || value != (id%2 == 0) {
			t.Fatalf("value %d=(%v,%v)", id, value, found)
		}
	}
}

func TestBooleanCNFAgreesWithTruthTables(t *testing.T) {
	random := rand.New(rand.NewSource(1))
	for example := 0; example < 2000; example++ {
		formula := randomBooleanTerm(random, 4)
		expected := truthTableSatisfiable(formula, 4)
		result := Check(Assert(1, New(), formula))
		model, sat := result.(Satisfiable)
		if sat != expected {
			t.Fatalf("example %d: result=%T, truth-table sat=%v", example, result, expected)
		}
		if sat {
			value, complete := BoolValue(model.Value, formula)
			if !complete || !value {
				t.Fatalf("example %d: returned model does not satisfy formula", example)
			}
		}
	}
}

func TestWatchedCDCLAgreesWithExhaustiveCNF(t *testing.T) {
	random := rand.New(rand.NewSource(17))
	for example := 0; example < 1000; example++ {
		const variables = 6
		clauses := make([][]int, 20)
		for clause := range clauses {
			width := 1 + random.Intn(4)
			clauses[clause] = make([]int, width)
			for index := range clauses[clause] {
				literal := 1 + random.Intn(variables)
				if random.Intn(2) == 0 {
					literal = -literal
				}
				clauses[clause][index] = literal
			}
		}
		solver, ok := watchedSolverForTest(variables, clauses)
		if !ok {
			if exhaustiveCNFSatisfiable(variables, clauses) {
				t.Fatalf("example %d rejected during initialization", example)
			}
			continue
		}
		got := solver.search()
		want := exhaustiveCNFSatisfiable(variables, clauses)
		if got != want {
			t.Fatalf("example %d: cdcl=%v exhaustive=%v clauses=%v", example, got, want, clauses)
		}
	}
}

func TestWatchedCDCLLearnsOnPigeonhole(t *testing.T) {
	const pigeons, holes = 5, 4
	clauses := pigeonholeCNF(pigeons, holes)
	solver, ok := watchedSolverForTest(pigeons*holes, clauses)
	if !ok {
		t.Fatal("pigeonhole rejected during initialization")
	}
	if solver.search() {
		t.Fatal("five pigeons unexpectedly fit into four holes")
	}
	if solver.learned == 0 || solver.conflicts == 0 {
		t.Fatalf("conflicts=%d learned=%d", solver.conflicts, solver.learned)
	}
}

func pigeonholeCNF(pigeons, holes int) [][]int {
	variable := func(pigeon, hole int) int { return pigeon*holes + hole + 1 }
	clauses := make([][]int, 0, pigeons+pigeons*holes*holes+holes*pigeons*pigeons)
	for pigeon := 0; pigeon < pigeons; pigeon++ {
		clause := make([]int, holes)
		for hole := 0; hole < holes; hole++ {
			clause[hole] = variable(pigeon, hole)
		}
		clauses = append(clauses, clause)
		for left := 0; left < holes; left++ {
			for right := left + 1; right < holes; right++ {
				clauses = append(clauses, []int{-variable(pigeon, left), -variable(pigeon, right)})
			}
		}
	}
	for hole := 0; hole < holes; hole++ {
		for left := 0; left < pigeons; left++ {
			for right := left + 1; right < pigeons; right++ {
				clauses = append(clauses, []int{-variable(left, hole), -variable(right, hole)})
			}
		}
	}
	return clauses
}

func TestWatchedCDCLBackjumpsOverIrrelevantDecision(t *testing.T) {
	// Decisions choose 1, 2, then 3. Variable 2 is irrelevant to the conflict:
	// 3 implies 4, while 1 and 3 together require not-4. First-UIP learning
	// therefore jumps from level 3 to level 1.
	clauses := [][]int{{-3, 4}, {-1, -3, -4}}
	solver, ok := watchedSolverForTest(4, clauses)
	if !ok || !solver.search() {
		t.Fatal("backjump fixture should remain satisfiable")
	}
	if solver.backjumps == 0 || solver.learned == 0 {
		t.Fatalf("backjumps=%d learned=%d", solver.backjumps, solver.learned)
	}
}

func TestWatchedCDCLRestartsAndUsesActivityOnHardConflictSet(t *testing.T) {
	const pigeons, holes = 7, 6
	solver, ok := watchedSolverForTest(pigeons*holes, pigeonholeCNF(pigeons, holes))
	if !ok || solver.search() {
		t.Fatal("seven pigeons unexpectedly fit into six holes")
	}
	if solver.restarts == 0 || solver.activity == nil {
		t.Fatalf("conflicts=%d restarts=%d activity=%v", solver.conflicts, solver.restarts, solver.activity != nil)
	}
	t.Logf("conflicts=%d learned=%d restarts=%d clauses=%d literals=%d", solver.conflicts, solver.learned, solver.restarts, len(solver.clauses), len(solver.literals))
}

func watchedSolverForTest(variableCount int, source [][]int) (*watchedSolver, bool) {
	literals := make([]int, 0)
	clauses := make([]cnfClause, len(source))
	for index, values := range source {
		start := len(literals)
		literals = append(literals, values...)
		clauses[index] = cnfClause{start: start, end: len(literals)}
	}
	return newWatchedSolver(variableCount, literals, clauses)
}

func exhaustiveCNFSatisfiable(variables int, clauses [][]int) bool {
	for assignment := 0; assignment < 1<<variables; assignment++ {
		all := true
		for _, clause := range clauses {
			satisfied := false
			for _, literal := range clause {
				value := assignment&(1<<(absCNF(literal)-1)) != 0
				if value == (literal > 0) {
					satisfied = true
					break
				}
			}
			if !satisfied {
				all = false
				break
			}
		}
		if all {
			return true
		}
	}
	return false
}

func TestImmutableSolverCheckIsConcurrent(t *testing.T) {
	a := BoolSymbol{ID: 1, Name: "a"}
	solver := Assert(1, New(), Or{Values: []Term[BoolSort]{a, Not{Value: a}}})
	var group sync.WaitGroup
	for worker := 0; worker < 32; worker++ {
		group.Add(1)
		go func() {
			defer group.Done()
			for iteration := 0; iteration < 100; iteration++ {
				if _, ok := Check(solver).(Satisfiable); !ok {
					t.Errorf("result=%T", Check(solver))
					return
				}
			}
		}()
	}
	group.Wait()
}

func TestMemoizedViewBuildsOnceConcurrently(t *testing.T) {
	solver := Assert(1, New(), Bool{Value: true})
	key := new(byte)
	var builds atomic.Int32
	var group sync.WaitGroup
	for worker := 0; worker < 32; worker++ {
		group.Add(1)
		go func() {
			defer group.Done()
			value := MemoizedView(solver, key, func(result CheckResult) any {
				builds.Add(1)
				return result
			})
			if _, ok := value.(Satisfiable); !ok {
				t.Errorf("view=%T", value)
			}
		}()
	}
	group.Wait()
	if builds.Load() != 1 {
		t.Fatalf("builds=%d", builds.Load())
	}
}

func TestMemoizedViewRejectsDifferentAdapter(t *testing.T) {
	solver := Assert(1, New(), Bool{Value: true})
	MemoizedView(solver, new(byte), func(result CheckResult) any { return result })
	defer func() {
		if recover() == nil {
			t.Fatal("different adapter key did not panic")
		}
	}()
	MemoizedView(solver, new(byte), func(result CheckResult) any { return result })
}

func randomBooleanTerm(random *rand.Rand, depth int) Term[BoolSort] {
	if depth == 0 {
		if random.Intn(5) == 0 {
			return Bool{Value: random.Intn(2) == 0}
		}
		return BoolSymbol{ID: random.Intn(4), Name: "variable"}
	}
	left := randomBooleanTerm(random, depth-1)
	right := randomBooleanTerm(random, depth-1)
	switch random.Intn(6) {
	case 0:
		return Not{Value: left}
	case 1:
		return And{Values: []Term[BoolSort]{left, right}}
	case 2:
		return Or{Values: []Term[BoolSort]{left, right}}
	case 3:
		return Implies{Left: left, Right: right}
	case 4:
		return Iff{Left: left, Right: right}
	default:
		return If[BoolSort]{Condition: left, Then: right, Else: Not{Value: right}}
	}
}

func truthTableSatisfiable(formula Term[BoolSort], variables int) bool {
	values := make(map[int]bool, variables)
	for assignment := 0; assignment < 1<<variables; assignment++ {
		for id := 0; id < variables; id++ {
			values[id] = assignment&(1<<id) != 0
		}
		if value, complete := evaluateBool(formula, booleanModel{external: values}, integerModel{}, rationalModel{}); complete && value {
			return true
		}
	}
	return false
}

func BenchmarkBooleanCoreWarm(b *testing.B) {
	a := BoolSymbol{ID: 1, Name: "a"}
	c := BoolSymbol{ID: 2, Name: "b"}
	formula := And{Values: []Term[BoolSort]{Or{Values: []Term[BoolSort]{a, c}}, Not{Value: a}}}
	solver := Assert(1, New(), formula)
	if _, ok := Check(solver).(Satisfiable); !ok {
		b.Fatal("unexpected result")
	}
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if _, ok := Check(solver).(Satisfiable); !ok {
			b.Fatal("unexpected result")
		}
	}
}

func BenchmarkBooleanCoreCold(b *testing.B) {
	a := BoolSymbol{ID: 1, Name: "a"}
	c := BoolSymbol{ID: 2, Name: "b"}
	formula := And{Values: []Term[BoolSort]{Or{Values: []Term[BoolSort]{a, c}}, Not{Value: a}}}
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		solver := Assert(1, New(), formula)
		if _, ok := Check(solver).(Satisfiable); !ok {
			b.Fatal("unexpected result")
		}
	}
}

func BenchmarkBooleanCoreSeventyVariablesCold(b *testing.B) {
	values := make([]Term[BoolSort], 70)
	for id := range values {
		values[id] = Iff{
			Left:  BoolSymbol{ID: id, Name: "value"},
			Right: Bool{Value: id%2 == 0},
		}
	}
	formula := And{Values: values}
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		solver := Assert(1, New(), formula)
		if _, ok := Check(solver).(Satisfiable); !ok {
			b.Fatal("unexpected result")
		}
	}
}

func BenchmarkBooleanPropagationChainCold(b *testing.B) {
	const variables = 256
	items := make([]Term[BoolSort], 0, variables+1)
	first := BoolSymbol{ID: 0, Name: "v0"}
	items = append(items, first)
	previous := Term[BoolSort](first)
	for id := 1; id < variables; id++ {
		next := Term[BoolSort](BoolSymbol{ID: id, Name: "v"})
		items = append(items, Implies{Left: previous, Right: next})
		previous = next
	}
	items = append(items, Not{Value: previous})
	formula := And{Values: items}
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		solver := Assert(1, New(), formula)
		if _, ok := Check(solver).(Unsatisfiable); !ok {
			b.Fatal("unexpected result")
		}
	}
}

func BenchmarkIntegerDifferenceChainCold(b *testing.B) {
	const variables = 256
	items := make([]Term[BoolSort], 0, variables)
	previous := Term[IntSort](IntSymbol{ID: 0, Name: "v0"})
	for id := 1; id < variables; id++ {
		next := Term[IntSort](IntSymbol{ID: id, Name: "v"})
		items = append(items, LessEqual{Left: Subtract{Left: previous, Right: next}, Right: Integer{Value: 1}})
		previous = next
	}
	items = append(items, LessEqual{Left: previous, Right: Integer{Value: 0}})
	formula := And{Values: items}
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		solver := Assert(1, New(), formula)
		if _, ok := Check(solver).(Satisfiable); !ok {
			b.Fatal("unexpected result")
		}
	}
}

func TestGroundEUFCongruence(t *testing.T) {
	a := UninterpretedConstant(1, 1, "a")
	c := UninterpretedConstant(1, 2, "b")
	f := DeclareUnaryFunction(1, 2, 1, "f")
	fa := ApplyUnary(f, a)
	fc := ApplyUnary(f, c)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: a, Right: c},
		Not{Value: Equal{Left: fa, Right: fc}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestCompactGroundEUFCongruence(t *testing.T) {
	a := UninterpretedEUFTerm{Kind: 1, SortID: 1, SymbolID: 1}
	b := UninterpretedEUFTerm{Kind: 1, SortID: 1, SymbolID: 2}
	fa := UninterpretedEUFTerm{Kind: 2, SortID: 1, FunctionID: 1, FirstSortID: 1, FirstID: 1}
	fb := UninterpretedEUFTerm{Kind: 2, SortID: 1, FunctionID: 1, FirstSortID: 1, FirstID: 2}
	formula := UninterpretedEUFConjunction{Count: 2}
	formula.Inline[0] = UninterpretedEUFRelation{Left: a, Right: b}
	formula.Inline[1] = UninterpretedEUFRelation{Left: fa, Right: fb, Negated: true}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("compact congruence contradiction must be unsatisfiable")
	}
}

func TestFiniteEnumerationDatatypeModelsAndRecognizers(t *testing.T) {
	red := DatatypeConstructor(7, 3, 0, "red")
	green := DatatypeConstructor(7, 3, 1, "green")
	x := DatatypeConst(7, 3, 1, "x")
	formula := And{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: x, Right: red}},
		IsDatatypeConstructor(7, 3, 1, x),
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%#v", Check(Assert(1, New(), formula)))
	}
	value, found := DatatypeModelValue(7, 3, result.Value, x)
	if !found || value.DatatypeID != 7 || value.ConstructorCount != 3 || value.ConstructorID != 1 {
		t.Fatalf("x=(%#v,%v)", value, found)
	}
	if direct, found := DatatypeModelValue(7, 3, result.Value, green); !found || direct.ConstructorID != 1 {
		t.Fatalf("green=(%#v,%v)", direct, found)
	}
	if recognized, found := BoolValue(result.Value, IsDatatypeConstructor(7, 3, 1, x)); !found || !recognized {
		t.Fatalf("is-green(x)=(%v,%v)", recognized, found)
	}
}

func TestFiniteEnumerationConstructorsAreDisjoint(t *testing.T) {
	red := DatatypeConstructor(8, 2, 0, "red")
	green := DatatypeConstructor(8, 2, 1, "green")
	if _, ok := Check(Assert(1, New(), Equal{Left: red, Right: green})).(Unsatisfiable); !ok {
		t.Fatal("distinct datatype constructors must not be equal")
	}
}

func TestFiniteEnumerationDatatypeColoringDetectsExhaustion(t *testing.T) {
	a := DatatypeConst(9, 2, 1, "a")
	b := DatatypeConst(9, 2, 2, "b")
	c := DatatypeConst(9, 2, 3, "c")
	formula := And{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: a, Right: b}},
		Not{Value: Equal{Left: a, Right: c}},
		Not{Value: Equal{Left: b, Right: c}},
	}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("three pairwise-distinct values cannot inhabit a two-constructor datatype")
	}
}

func TestFiniteEnumerationDatatypeBooleanStructure(t *testing.T) {
	red := DatatypeConstructor(701, 2, 0, "red")
	blue := DatatypeConstructor(701, 2, 1, "blue")
	x := DatatypeConst(701, 2, 1, "x")
	isRed := Equal{Left: x, Right: red}
	isBlue := Equal{Left: x, Right: blue}
	formula := And{Values: []Term[BoolSort]{
		Or{Values: []Term[BoolSort]{isRed, isBlue}},
		Implies{Left: isRed, Right: Not{Value: isBlue}},
		Iff{Left: isRed, Right: Not{Value: isBlue}},
		If[BoolSort]{Condition: isRed, Then: Bool{Value: true}, Else: isBlue},
		Not{Value: isRed},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("Boolean QF_DT result=%#v", result)
	}
	value, found := DatatypeModelValue(701, 2, result.Value, x)
	if !found || value.ConstructorID != 1 {
		t.Fatalf("Boolean QF_DT model=%+v found=%v", value, found)
	}

	contradiction := And{Values: []Term[BoolSort]{
		Or{Values: []Term[BoolSort]{isRed, isBlue}},
		Not{Value: Or{Values: []Term[BoolSort]{isRed, isBlue}}},
	}}
	if result := Check(Assert(2, New(), contradiction)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("Boolean QF_DT contradiction result=%#v", result)
	}
}

func TestFiniteEnumerationDatatypeBooleanBranchLimit(t *testing.T) {
	red := DatatypeConstructor(702, 2, 0, "red")
	blue := DatatypeConstructor(702, 2, 1, "blue")
	terms := make([]Term[BoolSort], 9)
	for index := range terms {
		x := DatatypeConst(702, 2, index+1, "x")
		terms[index] = Or{Values: []Term[BoolSort]{
			Equal{Left: x, Right: red},
			Equal{Left: x, Right: blue},
		}}
	}
	result, ok := Check(Assert(1, New(), And{Values: terms})).(Unknown)
	if !ok {
		t.Fatalf("Boolean QF_DT branch-limit result=%#v", result)
	}
	limit, ok := result.Reason.(ResourceLimit)
	if !ok || limit.Limit != datatypeBooleanBranchLimit {
		t.Fatalf("Boolean QF_DT branch-limit reason=%#v", result.Reason)
	}
}

func TestRecursiveUnaryDatatypeConstructorsSelectorsAndModels(t *testing.T) {
	zero := DatatypeConstructor(10, 2, 0, "zero")
	succ := DeclareRecursiveDatatypeConstructor(10, 2, 1, "succ", "pred")
	one := ApplyRecursiveDatatypeConstructor(succ, zero)
	two := ApplyRecursiveDatatypeConstructor(succ, one)
	x := DatatypeConst(10, 2, 1, "x")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: two},
		IsRecursiveDatatypeConstructor(succ, x),
		Equal{Left: SelectRecursiveDatatypeConstructor(succ, x), Right: one},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		checked := Check(Assert(1, New(), formula))
		if unknown, unknownOK := checked.(Unknown); unknownOK {
			t.Fatalf("result=%T reason=%#v", checked, unknown.Reason)
		}
		t.Fatalf("result=%#v", checked)
	}
	value, found := DatatypeModelValue(10, 2, result.Value, x)
	if !found || value.ConstructorID != 1 || value.Child == nil || value.Child.ConstructorID != 1 || value.Child.Child == nil || value.Child.Child.ConstructorID != 0 {
		t.Fatalf("x=(%#v,%v)", value, found)
	}
	predecessor, found := DatatypeModelValue(10, 2, result.Value, SelectRecursiveDatatypeConstructor(succ, x))
	if !found || predecessor.ConstructorID != 1 || predecessor.Child == nil || predecessor.Child.ConstructorID != 0 {
		t.Fatalf("pred(x)=(%#v,%v)", predecessor, found)
	}
}

func TestRecursiveUnaryDatatypeInjectivityAndAcyclicity(t *testing.T) {
	succ := DeclareRecursiveDatatypeConstructor(11, 2, 1, "succ", "pred")
	x := DatatypeConst(11, 2, 1, "x")
	y := DatatypeConst(11, 2, 2, "y")
	injective := And{Values: []Term[BoolSort]{
		Equal{Left: ApplyRecursiveDatatypeConstructor(succ, x), Right: ApplyRecursiveDatatypeConstructor(succ, y)},
		Not{Value: Equal{Left: x, Right: y}},
	}}
	if _, ok := Check(Assert(1, New(), injective)).(Unsatisfiable); !ok {
		t.Fatal("equal recursive constructors must have equal fields")
	}
	cycle := Equal{Left: x, Right: ApplyRecursiveDatatypeConstructor(succ, x)}
	if _, ok := Check(Assert(2, New(), cycle)).(Unsatisfiable); !ok {
		t.Fatal("recursive datatype values must be finite")
	}
}

func TestRecursiveUnaryDatatypeDisequalityMayShareConstructor(t *testing.T) {
	solver := New()
	zero := DatatypeConstructor(83, 2, 0, "zero")
	succ := DeclareRecursiveDatatypeConstructor(83, 2, 1, "succ", "pred")
	one := ApplyRecursiveDatatypeConstructor(succ, zero)
	two := ApplyRecursiveDatatypeConstructor(succ, one)
	three := ApplyRecursiveDatatypeConstructor(succ, two)
	x := DatatypeConst(83, 2, 1, "x")
	formula := And{
		Values: []Term[BoolSort]{
			Equal{Left: x, Right: ApplyRecursiveDatatypeConstructor(succ, three)},
			Not{Value: Equal{Left: SelectRecursiveDatatypeConstructor(succ, x), Right: two}},
		},
	}
	if _, ok := Check(Assert(1, solver, formula)).(Satisfiable); !ok {
		t.Fatalf("different recursive depths with the same outer constructor must remain satisfiable")
	}
}

func TestRecursiveUnaryDatatypeRecognizerBuildsWellFoundedModel(t *testing.T) {
	succ := DeclareRecursiveDatatypeConstructor(84, 2, 1, "succ", "pred")
	x := DatatypeConst(84, 2, 1, "x")
	result, ok := Check(Assert(1, New(), IsRecursiveDatatypeConstructor(succ, x))).(Satisfiable)
	if !ok {
		t.Fatalf("recursive recognizer result=%#v", Check(Assert(1, New(), IsRecursiveDatatypeConstructor(succ, x))))
	}
	value, found := DatatypeModelValue(84, 2, result.Value, x)
	if !found || value.ConstructorID != 1 || value.ConstructorName != "succ" || value.Child == nil || value.Child.ConstructorID != 0 || value.Child.Child != nil {
		t.Fatalf("recursive recognizer model=%#v/%v", value, found)
	}
}

func TestBinaryRecursiveDatatypeSelectorsAndModels(t *testing.T) {
	leaf := DatatypeConstructor(85, 2, 0, "leaf")
	node := DeclareBinaryRecursiveDatatypeConstructor(85, 2, 1, "node", "left", "right")
	left := ApplyBinaryRecursiveDatatypeConstructor(node, leaf, leaf)
	tree := ApplyBinaryRecursiveDatatypeConstructor(node, left, leaf)
	x := DatatypeConst(85, 2, 1, "x")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: tree},
		Equal{Left: SelectBinaryRecursiveDatatypeConstructor(FirstDatatypeField{}, node, x), Right: left},
		Equal{Left: SelectBinaryRecursiveDatatypeConstructor(SecondDatatypeField{}, node, x), Right: leaf},
		IsBinaryRecursiveDatatypeConstructor(node, x),
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("binary recursive result=%#v", Check(Assert(1, New(), formula)))
	}
	value, found := DatatypeModelValue(85, 2, result.Value, x)
	if !found || value.ConstructorID != 1 || value.Child == nil || value.SecondChild == nil || value.Child.ConstructorID != 1 || value.Child.Child == nil || value.Child.SecondChild == nil || value.SecondChild.ConstructorID != 0 {
		t.Fatalf("binary recursive model=%#v/%v", value, found)
	}
}

func TestBinaryRecursiveDatatypeInjectivityAndAcyclicity(t *testing.T) {
	leaf := DatatypeConstructor(86, 2, 0, "leaf")
	node := DeclareBinaryRecursiveDatatypeConstructor(86, 2, 1, "node", "left", "right")
	x := DatatypeConst(86, 2, 1, "x")
	y := DatatypeConst(86, 2, 2, "y")
	firstConflict := And{Values: []Term[BoolSort]{
		Equal{Left: ApplyBinaryRecursiveDatatypeConstructor(node, x, leaf), Right: ApplyBinaryRecursiveDatatypeConstructor(node, y, leaf)},
		Not{Value: Equal{Left: x, Right: y}},
	}}
	if _, ok := Check(Assert(1, New(), firstConflict)).(Unsatisfiable); !ok {
		t.Fatal("binary constructor must be injective in its first field")
	}
	secondConflict := And{Values: []Term[BoolSort]{
		Equal{Left: ApplyBinaryRecursiveDatatypeConstructor(node, leaf, x), Right: ApplyBinaryRecursiveDatatypeConstructor(node, leaf, y)},
		Not{Value: Equal{Left: x, Right: y}},
	}}
	if _, ok := Check(Assert(2, New(), secondConflict)).(Unsatisfiable); !ok {
		t.Fatal("binary constructor must be injective in its second field")
	}
	cycle := Equal{Left: x, Right: ApplyBinaryRecursiveDatatypeConstructor(node, leaf, x)}
	if _, ok := Check(Assert(3, New(), cycle)).(Unsatisfiable); !ok {
		t.Fatal("cycles through either binary field must be rejected")
	}
}

func TestBinaryRecursiveDatatypeRecognizerBuildsWellFoundedModel(t *testing.T) {
	node := DeclareBinaryRecursiveDatatypeConstructor(87, 2, 1, "node", "left", "right")
	x := DatatypeConst(87, 2, 1, "x")
	result, ok := Check(Assert(1, New(), IsBinaryRecursiveDatatypeConstructor(node, x))).(Satisfiable)
	if !ok {
		t.Fatalf("binary recognizer result=%#v", Check(Assert(1, New(), IsBinaryRecursiveDatatypeConstructor(node, x))))
	}
	value, found := DatatypeModelValue(87, 2, result.Value, x)
	if !found || value.ConstructorID != 1 || value.Child == nil || value.SecondChild == nil || value.Child.ConstructorID != 0 || value.SecondChild.ConstructorID != 0 {
		t.Fatalf("binary recognizer model=%#v/%v", value, found)
	}
}

func TestNaryRecursiveDatatypeSelectorsAndModels(t *testing.T) {
	leaf := DatatypeConstructor(88, 2, 0, "leaf")
	branch := DeclareNaryRecursiveDatatypeConstructor(88, 2, 1, 3, "branch", ternaryDatatypeNames())
	nested := ApplyNaryRecursiveDatatypeConstructor(branch, ternaryDatatypeValues(leaf, leaf, leaf))
	tree := ApplyNaryRecursiveDatatypeConstructor(branch, ternaryDatatypeValues(leaf, nested, leaf))
	x := DatatypeConst(88, 2, 1, "x")
	third := vec.Succ{Prev: vec.Succ{Prev: vec.Zero{}}}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: tree},
		Equal{Left: SelectNaryRecursiveDatatypeConstructor(vec.Zero{}, branch, x), Right: leaf},
		Equal{Left: SelectNaryRecursiveDatatypeConstructor(vec.Succ{Prev: vec.Zero{}}, branch, x), Right: nested},
		Equal{Left: SelectNaryRecursiveDatatypeConstructor(third, branch, x), Right: leaf},
		IsNaryRecursiveDatatypeConstructor(branch, x),
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("n-ary recursive result=%#v", Check(Assert(1, New(), formula)))
	}
	value, found := DatatypeModelValue(88, 2, result.Value, x)
	first, firstOK := value.Children.At(0)
	second, secondOK := value.Children.At(1)
	thirdValue, thirdOK := value.Children.At(2)
	if !found || value.ConstructorID != 1 || value.Children.Len() != 3 || !firstOK || first.ConstructorID != 0 || !secondOK || second.ConstructorID != 1 || second.Children.Len() != 3 || !thirdOK || thirdValue.ConstructorID != 0 {
		t.Fatalf("n-ary recursive model=%#v/%v", value, found)
	}
}

func TestNaryRecursiveDatatypeInjectivityAndAcyclicity(t *testing.T) {
	leaf := DatatypeConstructor(89, 2, 0, "leaf")
	branch := DeclareNaryRecursiveDatatypeConstructor(89, 2, 1, 3, "branch", ternaryDatatypeNames())
	x := DatatypeConst(89, 2, 1, "x")
	y := DatatypeConst(89, 2, 2, "y")
	left := ApplyNaryRecursiveDatatypeConstructor(branch, ternaryDatatypeValues(leaf, leaf, x))
	right := ApplyNaryRecursiveDatatypeConstructor(branch, ternaryDatatypeValues(leaf, leaf, y))
	injective := And{Values: []Term[BoolSort]{Equal{Left: left, Right: right}, Not{Value: Equal{Left: x, Right: y}}}}
	if _, ok := Check(Assert(1, New(), injective)).(Unsatisfiable); !ok {
		t.Fatal("n-ary constructor must be injective in every field")
	}
	cycle := Equal{Left: x, Right: ApplyNaryRecursiveDatatypeConstructor(branch, ternaryDatatypeValues(leaf, leaf, x))}
	if _, ok := Check(Assert(2, New(), cycle)).(Unsatisfiable); !ok {
		t.Fatal("cycles through any n-ary field must be rejected")
	}
}

func mixedIntSelfSignature() MixedDatatypeSignature {
	return IntDatatypeField("payload", SelfDatatypeField("next", EmptyMixedDatatypeSignature{}))
}

func mixedIntSelfArguments(payload Term[IntSort], next Term[DatatypeSort]) MixedDatatypeArguments {
	return IntDatatypeArgument(payload, SelfDatatypeArgument(next, EmptyMixedDatatypeArguments{}))
}

func TestMixedRecursiveDatatypeSelectorsAndExactModel(t *testing.T) {
	leaf := DatatypeConstructor(90, 2, 0, "leaf")
	node := DeclareMixedRecursiveDatatypeConstructor(90, 2, 1, "node", mixedIntSelfSignature())
	nested := ApplyMixedRecursiveDatatypeConstructor(node, mixedIntSelfArguments(Integer{Value: 42}, leaf))
	x := DatatypeConst(90, 2, 1, "x")
	fields := MixedDatatypeFields(node)
	next := NextMixedDatatypeField(fields)
	formula := And{
		Values: []Term[BoolSort]{
			Equal{Left: x, Right: nested},
			Equal{Left: SelectMixedIntDatatypeField(fields, x), Right: Integer{Value: 42}},
			Equal{Left: SelectMixedSelfDatatypeField(next, x), Right: leaf},
			IsMixedRecursiveDatatypeConstructor(node, x),
		},
	}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		checked := Check(Assert(1, New(), formula))
		if unknown, unknownOK := checked.(Unknown); unknownOK {
			t.Fatalf("result=%T reason=%#v", checked, unknown.Reason)
		}
		t.Fatalf("result=%#v", checked)
	}
	value, found := DatatypeModelValue(90, 2, result.Value, x)
	if !found || value.ConstructorID != 1 || value.Fields.Len() != 2 {
		t.Fatalf("value=%+v found=%v", value, found)
	}
	payload, _ := value.Fields.At(0)
	child, _ := value.Fields.At(1)
	if CompareIntegerValue(payload.Integer, NewIntegerValue(42)) != 0 || child.Datatype == nil || child.Datatype.ConstructorID != 0 {
		t.Fatalf("payload=%+v child=%+v", payload, child)
	}
}

func TestMixedRecursiveDatatypeNegatedScalarSelectorEquality(t *testing.T) {
	leaf := DatatypeConstructor(91, 2, 0, "leaf")
	node := DeclareMixedRecursiveDatatypeConstructor(91, 2, 1, "node", mixedIntSelfSignature())
	x := DatatypeConst(91, 2, 1, "x")
	fields := MixedDatatypeFields(node)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: ApplyMixedRecursiveDatatypeConstructor(node, mixedIntSelfArguments(Integer{Value: 42}, leaf))},
		Not{Value: Equal{Left: SelectMixedIntDatatypeField(fields, x), Right: Integer{Value: 42}}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("negated selector equality contradiction result=%#v", result)
	}
}

func TestMixedRecursiveDatatypeScalarConditional(t *testing.T) {
	leaf := DatatypeConstructor(92, 2, 0, "nil")
	cons := DeclareMixedRecursiveDatatypeConstructor(92, 2, 1, "cons", mixedIntSelfSignature())
	x := DatatypeConst(92, 2, 1, "x")
	fields := MixedDatatypeFields(cons)
	application := ApplyMixedRecursiveDatatypeConstructor(cons, mixedIntSelfArguments(Integer{Value: 42}, leaf))
	matched := If[IntSort]{
		Condition: IsDatatypeConstructor(92, 2, 0, x),
		Then:      Integer{Value: 0},
		Else:      SelectMixedIntDatatypeField(fields, x),
	}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: application},
		Equal{Left: matched, Right: Integer{Value: 42}},
	}}
	if !containsDatatypeTheory(formula) || !containsMixedDatatypeTheory(formula) {
		t.Fatal("datatype scalar conditional must route through mixed QF_DT")
	}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("datatype scalar conditional result=%#v", result)
	}
}

func TestMixedRecursiveDatatypeScalarConditionalChoosesConstructor(t *testing.T) {
	cons := DeclareMixedRecursiveDatatypeConstructor(920, 2, 1, "cons", mixedIntSelfSignature())
	x := DatatypeConst(920, 2, 1, "x")
	fields := MixedDatatypeFields(cons)
	matched := If[IntSort]{
		Condition: IsDatatypeConstructor(920, 2, 0, x),
		Then:      Integer{Value: 0},
		Else:      SelectMixedIntDatatypeField(fields, x),
	}
	result, ok := Check(Assert(1, New(), Equal{Left: matched, Right: Integer{Value: 42}})).(Satisfiable)
	if !ok {
		t.Fatalf("unconstrained datatype match result=%#v", result)
	}
	value, found := DatatypeModelValue(920, 2, result.Value, x)
	if !found || value.ConstructorID != 1 || value.Fields.Len() != 2 {
		t.Fatalf("unconstrained datatype match value=%+v found=%v", value, found)
	}
	head, _ := value.Fields.At(0)
	tail, _ := value.Fields.At(1)
	if CompareIntegerValue(head.Integer, NewIntegerValue(42)) != 0 || tail.Datatype == nil || tail.Datatype.ConstructorID != 0 {
		t.Fatalf("unconstrained datatype match head=%+v tail=%+v", head, tail)
	}
}

func TestMixedRecursiveDatatypeUpdateField(t *testing.T) {
	leaf := DatatypeConstructor(93, 2, 0, "nil")
	cons := DeclareMixedRecursiveDatatypeConstructor(93, 2, 1, "cons", mixedIntSelfSignature())
	x := DatatypeConst(93, 2, 1, "x")
	fields := MixedDatatypeFields(cons)
	updated := UpdateMixedIntDatatypeField(fields, x, Integer{Value: 7})
	want := ApplyMixedRecursiveDatatypeConstructor(cons, mixedIntSelfArguments(Integer{Value: 7}, leaf))
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: ApplyMixedRecursiveDatatypeConstructor(cons, mixedIntSelfArguments(Integer{Value: 42}, leaf))},
		Equal{Left: updated, Right: want},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("matching update-field result=%#v", result)
	}

	identity := Equal{Left: UpdateMixedIntDatatypeField(fields, leaf, Integer{Value: 9}), Right: leaf}
	if result := Check(Assert(2, New(), identity)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("nonmatching update-field identity result=%#v", result)
	}

	contradiction := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: ApplyMixedRecursiveDatatypeConstructor(cons, mixedIntSelfArguments(Integer{Value: 42}, leaf))},
		Not{Value: Equal{Left: updated, Right: want}},
	}}
	if result := Check(Assert(3, New(), contradiction)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("update-field contradiction result=%#v", result)
	}

	symbolic := DatatypeConst(93, 2, 2, "symbolic")
	symbolicUpdate := UpdateMixedIntDatatypeField(fields, symbolic, Integer{Value: 11})
	symbolicFormula := And{Values: []Term[BoolSort]{
		IsMixedRecursiveDatatypeConstructor(cons, symbolic),
		Equal{Left: SelectMixedIntDatatypeField(fields, symbolicUpdate), Right: Integer{Value: 11}},
	}}
	symbolicResult, ok := Check(Assert(4, New(), symbolicFormula)).(Satisfiable)
	if !ok {
		t.Fatalf("symbolic update-field result=%#v", Check(Assert(4, New(), symbolicFormula)))
	}
	symbolicValue, found := DatatypeModelValue(93, 2, symbolicResult.Value, symbolicUpdate)
	payload, payloadOK := symbolicValue.Fields.At(0)
	payloadInteger, payloadFits := payload.Integer.Int64()
	if !found || symbolicValue.ConstructorID != 1 || !payloadOK || !payloadFits || payloadInteger != 11 {
		t.Fatalf("symbolic updated value=%+v found=%v", symbolicValue, found)
	}
}

func TestMixedRecursiveDatatypeInjectivityAndAcyclicity(t *testing.T) {
	leaf := DatatypeConstructor(91, 2, 0, "leaf")
	node := DeclareMixedRecursiveDatatypeConstructor(91, 2, 1, "node", mixedIntSelfSignature())
	first := ApplyMixedRecursiveDatatypeConstructor(node, mixedIntSelfArguments(Integer{Value: 1}, leaf))
	second := ApplyMixedRecursiveDatatypeConstructor(node, mixedIntSelfArguments(Integer{Value: 2}, leaf))
	if _, ok := Check(Assert(1, New(), Equal{Left: first, Right: second})).(Unsatisfiable); !ok {
		t.Fatal("mixed scalar-field injectivity violation was satisfiable")
	}
	x := DatatypeConst(91, 2, 2, "x")
	cycle := Equal{Left: x, Right: ApplyMixedRecursiveDatatypeConstructor(node, mixedIntSelfArguments(Integer{Value: 1}, x))}
	if _, ok := Check(Assert(1, New(), cycle)).(Unsatisfiable); !ok {
		t.Fatal("mixed recursive cycle was satisfiable")
	}
}

func TestMixedRecursiveDatatypeRecognizerBuildsExactDefaultModel(t *testing.T) {
	node := DeclareMixedRecursiveDatatypeConstructor(92, 2, 1, "node", mixedIntSelfSignature())
	x := DatatypeConst(92, 2, 1, "x")
	result, ok := Check(Assert(1, New(), IsMixedRecursiveDatatypeConstructor(node, x))).(Satisfiable)
	if !ok {
		t.Fatalf("mixed recognizer result=%#v", Check(Assert(1, New(), IsMixedRecursiveDatatypeConstructor(node, x))))
	}
	value, found := DatatypeModelValue(92, 2, result.Value, x)
	payload, payloadOK := value.Fields.At(0)
	child, childOK := value.Fields.At(1)
	if !found || value.ConstructorID != 1 || value.Fields.Len() != 2 || !payloadOK || CompareIntegerValue(payload.Integer, NewIntegerValue(0)) != 0 || !childOK || child.Datatype == nil || child.Datatype.ConstructorID != 0 {
		t.Fatalf("mixed recognizer model=%+v found=%v", value, found)
	}
}

func TestMixedRecursiveDatatypeSupportsEveryScalarFieldSortTogether(t *testing.T) {
	signature := BoolDatatypeField("flag",
		IntDatatypeField("count",
			RealDatatypeField("weight",
				BitVecDatatypeField(8, "bits",
					SelfDatatypeField("next", EmptyMixedDatatypeSignature{})))))
	leaf := DatatypeConstructor(93, 2, 0, "leaf")
	node := DeclareMixedRecursiveDatatypeConstructor(93, 2, 1, "node", signature)
	arguments := BoolDatatypeArgument(Bool{Value: true},
		IntDatatypeArgument(Integer{Value: 7},
			RealDatatypeArgument(Real{Value: NewRational(3, 2)},
				BitVecDatatypeArgument(8, BitVecVal(8, 0xa5),
					SelfDatatypeArgument(leaf, EmptyMixedDatatypeArguments{})))))
	valueTerm := ApplyMixedRecursiveDatatypeConstructor(node, arguments)
	x := DatatypeConst(93, 2, 1, "x")
	flag := MixedDatatypeFields(node)
	count := NextMixedDatatypeField(flag)
	weight := NextMixedDatatypeField(count)
	bits := NextMixedDatatypeField(weight)
	next := NextMixedDatatypeField(bits)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: valueTerm},
		Equal{Left: SelectMixedBoolDatatypeField(flag, x), Right: Bool{Value: true}},
		Equal{Left: SelectMixedIntDatatypeField(count, x), Right: Integer{Value: 7}},
		Equal{Left: SelectMixedRealDatatypeField(weight, x), Right: Real{Value: NewRational(3, 2)}},
		Equal{Left: SelectMixedBitVecDatatypeField(8, bits, x), Right: BitVecVal(8, 0xa5)},
		Equal{Left: SelectMixedSelfDatatypeField(next, x), Right: leaf},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("mixed all-sort result=%#v", Check(Assert(1, New(), formula)))
	}
	value, found := DatatypeModelValue(93, 2, result.Value, x)
	if !found || value.Fields.Len() != 5 {
		t.Fatalf("mixed all-sort model=%+v found=%v", value, found)
	}
	flagValue, _ := value.Fields.At(0)
	countValue, _ := value.Fields.At(1)
	weightValue, _ := value.Fields.At(2)
	bitsValue, _ := value.Fields.At(3)
	nextValue, _ := value.Fields.At(4)
	if !flagValue.Boolean || CompareIntegerValue(countValue.Integer, NewIntegerValue(7)) != 0 || CompareRational(weightValue.Real, NewRational(3, 2)) != 0 || !EqualBitVectorValue(bitsValue.BitVector, NewBitVectorUint64(8, 0xa5)) || nextValue.Datatype == nil || nextValue.Datatype.ConstructorID != 0 {
		t.Fatalf("mixed all-sort fields=%+v", value.Fields)
	}
}

func TestMutuallyRecursiveDatatypeReferencesAndAcyclicity(t *testing.T) {
	treeLeaf := DatatypeConstructor(100, 2, 0, "leaf")
	forestNil := DatatypeConstructor(101, 2, 0, "nil")
	treeNode := DeclareMixedRecursiveDatatypeConstructor(100, 2, 1, "node",
		DatatypeReferenceField(101, 2, "children", EmptyMixedDatatypeSignature{}))
	forestCons := DeclareMixedRecursiveDatatypeConstructor(101, 2, 1, "cons",
		DatatypeReferenceField(100, 2, "head", SelfDatatypeField("tail", EmptyMixedDatatypeSignature{})))
	forestValue := ApplyMixedRecursiveDatatypeConstructor(forestCons,
		DatatypeReferenceArgument(100, 2, treeLeaf, SelfDatatypeArgument(forestNil, EmptyMixedDatatypeArguments{})))
	treeValue := ApplyMixedRecursiveDatatypeConstructor(treeNode,
		DatatypeReferenceArgument(101, 2, forestValue, EmptyMixedDatatypeArguments{}))
	x := DatatypeConst(100, 2, 1, "x")
	children := MixedDatatypeFields(treeNode)
	head := MixedDatatypeFields(forestCons)
	tail := NextMixedDatatypeField(head)
	selectedForest := SelectMixedDatatypeReferenceField(101, 2, children, x)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: treeValue},
		Equal{Left: SelectMixedDatatypeReferenceField(100, 2, head, selectedForest), Right: treeLeaf},
		Equal{Left: SelectMixedSelfDatatypeField(tail, selectedForest), Right: forestNil},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("mutual datatype result=%#v", Check(Assert(1, New(), formula)))
	}
	model, found := DatatypeModelValue(100, 2, result.Value, x)
	forestField, forestOK := model.Fields.At(0)
	if !found || !forestOK || forestField.Datatype == nil {
		t.Fatalf("mutual datatype model=%+v found=%v", model, found)
	}
	headField, headOK := forestField.Datatype.Fields.At(0)
	tailField, tailOK := forestField.Datatype.Fields.At(1)
	if forestField.Datatype.ConstructorID != 1 || !headOK || headField.Datatype == nil || headField.Datatype.ConstructorID != 0 || !tailOK || tailField.Datatype == nil || tailField.Datatype.ConstructorID != 0 {
		t.Fatalf("mutual datatype model=%+v found=%v", model, found)
	}
	treeVar := DatatypeConst(100, 2, 2, "tree")
	forestVar := DatatypeConst(101, 2, 2, "forest")
	cyclicTree := ApplyMixedRecursiveDatatypeConstructor(treeNode, DatatypeReferenceArgument(101, 2, forestVar, EmptyMixedDatatypeArguments{}))
	cyclicForest := ApplyMixedRecursiveDatatypeConstructor(forestCons, DatatypeReferenceArgument(100, 2, treeVar, SelfDatatypeArgument(forestNil, EmptyMixedDatatypeArguments{})))
	cycle := And{Values: []Term[BoolSort]{Equal{Left: treeVar, Right: cyclicTree}, Equal{Left: forestVar, Right: cyclicForest}}}
	if _, ok := Check(Assert(2, New(), cycle)).(Unsatisfiable); !ok {
		t.Fatal("cycles across mutually recursive datatype declarations must be rejected")
	}
}

func TestNaryRecursiveDatatypeRecognizerBuildsWellFoundedModel(t *testing.T) {
	branch := DeclareNaryRecursiveDatatypeConstructor(90, 2, 1, 3, "branch", ternaryDatatypeNames())
	x := DatatypeConst(90, 2, 1, "x")
	result, ok := Check(Assert(1, New(), IsNaryRecursiveDatatypeConstructor(branch, x))).(Satisfiable)
	if !ok {
		t.Fatalf("n-ary recognizer result=%#v", Check(Assert(1, New(), IsNaryRecursiveDatatypeConstructor(branch, x))))
	}
	value, found := DatatypeModelValue(90, 2, result.Value, x)
	first, firstOK := value.Children.At(0)
	second, secondOK := value.Children.At(1)
	third, thirdOK := value.Children.At(2)
	if !found || value.ConstructorID != 1 || value.Children.Len() != 3 || !firstOK || first.ConstructorID != 0 || !secondOK || second.ConstructorID != 0 || !thirdOK || third.ConstructorID != 0 {
		t.Fatalf("n-ary recognizer model=%#v/%v", value, found)
	}
}

func TestGroundEUFAllowsNonInjectiveFunctions(t *testing.T) {
	a := UninterpretedConstant(1, 1, "a")
	c := UninterpretedConstant(1, 2, "b")
	f := DeclareUnaryFunction(1, 2, 1, "f")
	formula := And{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: a, Right: c}},
		Equal{Left: ApplyUnary(f, a), Right: ApplyUnary(f, c)},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestGroundBinaryEUFCongruence(t *testing.T) {
	a := UninterpretedConstant(1, 1, "a")
	aPrime := UninterpretedConstant(1, 2, "a-prime")
	b := UninterpretedConstant(2, 3, "b")
	bPrime := UninterpretedConstant(2, 4, "b-prime")
	combine := DeclareBinaryFunction(1, 2, 3, 5, "combine")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: a, Right: aPrime},
		Equal{Left: b, Right: bPrime},
		Not{Value: Equal{Left: ApplyBinary(combine, a, b), Right: ApplyBinary(combine, aPrime, bPrime)}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestDisjointEUFLinearRealCombinationReturnsBothDecisionAndModel(t *testing.T) {
	a := UninterpretedConstant(1, 1, "a")
	b := UninterpretedConstant(1, 2, "b")
	function := DeclareUnaryFunction(1, 1, 3, "f")
	x := RealSymbol{ID: 4, Name: "x"}
	formula := And{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: a, Right: b}},
		Equal{Left: ApplyUnary(function, a), Right: ApplyUnary(function, b)},
		RealLessEqual{Left: Real{Value: NewRational(1, 1)}, Right: x},
		RealLessEqual{Left: x, Right: Real{Value: NewRational(2, 1)}},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		checked := Check(Assert(1, New(), formula))
		if unknown, unknownOK := checked.(Unknown); unknownOK {
			t.Fatalf("result=%T reason=%#v", checked, unknown.Reason)
		}
		t.Fatalf("result=%#v", checked)
	}
	value, found := RealValue(result.Value, x)
	if !found || rationalCmp(value, NewRational(1, 1)) < 0 || rationalCmp(value, NewRational(2, 1)) > 0 {
		t.Fatalf("x=%s/%v", value, found)
	}
}

func TestDisjointEUFLinearRealCombinationPropagatesUnsat(t *testing.T) {
	a := UninterpretedConstant(1, 1, "a")
	b := UninterpretedConstant(1, 2, "b")
	function := DeclareUnaryFunction(1, 1, 3, "f")
	x := RealSymbol{ID: 4, Name: "x"}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: a, Right: b},
		Not{Value: Equal{Left: ApplyUnary(function, a), Right: ApplyUnary(function, b)}},
		RealLessEqual{Left: x, Right: Real{Value: NewRational(2, 1)}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestDisjointIntegerAndRealCombinationMergesModels(t *testing.T) {
	i := IntSymbol{ID: 1, Name: "i"}
	x := RealSymbol{ID: 2, Name: "x"}
	formula := And{Values: []Term[BoolSort]{
		LessEqual{Left: Integer{Value: 3}, Right: i},
		LessEqual{Left: i, Right: Integer{Value: 4}},
		RealLessEqual{Left: Real{Value: NewRational(1, 2)}, Right: x},
		RealLessEqual{Left: x, Right: Real{Value: NewRational(3, 2)}},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, New(), formula)))
	}
	integer, integerOK := IntValue(result.Value, i)
	real, realOK := RealValue(result.Value, x)
	if !integerOK || integer < 3 || integer > 4 || !realOK || rationalCmp(real, NewRational(1, 2)) < 0 || rationalCmp(real, NewRational(3, 2)) > 0 {
		t.Fatalf("i=%d/%v x=%s/%v", integer, integerOK, real, realOK)
	}
}

func TestRealSortedUnaryFunctionCongruence(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	function := DeclareRealUnaryFunction(3, "f")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		Not{Value: Equal{Left: ApplySortedUnary(function, x), Right: ApplySortedUnary(function, y)}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestIntegerSortedFunctionCongruence(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	unary := DeclareIntUnaryFunction(3, "f")
	binary := DeclareIntBinaryFunction(4, "combine")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		Not{Value: Equal{Left: ApplySortedUnary(unary, x), Right: ApplySortedUnary(unary, y)}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("unary result=%T", result)
	}
	formula = And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		Not{Value: Equal{Left: ApplySortedBinary(binary, x, y), Right: ApplySortedBinary(binary, y, x)}},
	}}
	if result := Check(Assert(2, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("binary result=%T", result)
	}
	constant := Integer{Value: 7}
	constantFormula := Not{Value: Equal{
		Left:  ApplySortedUnary(unary, constant),
		Right: ApplySortedUnary(unary, constant),
	}}
	if result := Check(Assert(3, New(), constantFormula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("constant result=%T", result)
	}
	compact := TheoryConjunction{AtomCount: 2}
	compact.Atoms[0] = Equal{Left: x, Right: y}
	compact.Atoms[1] = UninterpretedEUFRelation{
		Left: UninterpretedEUFTerm{
			Kind: 3, SortID: -2, FunctionID: 4,
			FirstSortID: -2, SecondSortID: -2, FirstID: 1, SecondID: 2,
		},
		Right: UninterpretedEUFTerm{
			Kind: 3, SortID: -2, FunctionID: 4,
			FirstSortID: -2, SecondSortID: -2, FirstID: 2, SecondID: 1,
		},
	}
	compact.AtomNegated[1] = true
	if result := Check(Assert(4, New(), compact)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("compact result=%T", result)
	}
}

func TestSharedIntegerEUFExchangesLIAEquality(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	function := DeclareIntUnaryFunction(3, "f")
	formula := And{Values: []Term[BoolSort]{
		LessEqual{Left: x, Right: y},
		LessEqual{Left: y, Right: x},
		Not{Value: Equal{
			Left:  ApplySortedUnary(function, x),
			Right: ApplySortedUnary(function, y),
		}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedIntegerEUFPurifiesApplicationsInsideArithmetic(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	zero := Integer{Value: 0}
	function := DeclareIntUnaryFunction(3, "f")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		LessEqual{Left: ApplySortedUnary(function, x), Right: zero},
		Less{Left: zero, Right: ApplySortedUnary(function, y)},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedIntegerEUFPurifiesBinaryAffineArguments(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	one := Integer{Value: 1}
	zero := Integer{Value: 0}
	function := DeclareIntBinaryFunction(3, "combine")
	left := ApplySortedBinary(function, Add{Values: []Term[IntSort]{x, one}}, y)
	right := ApplySortedBinary(function, Add{Values: []Term[IntSort]{y, one}}, x)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		LessEqual{Left: left, Right: zero},
		Less{Left: zero, Right: right},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedIntegerEUFPurifiesTernaryAffineArguments(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	z := IntegerVariable(3)
	one := Integer{Value: 1}
	zero := Integer{Value: 0}
	function := DeclareIntTernaryFunction(4, "combine3")
	left := ApplySortedTernary(function, Add{Values: []Term[IntSort]{x, one}}, y, z)
	right := ApplySortedTernary(function, Add{Values: []Term[IntSort]{y, one}}, x, z)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		LessEqual{Left: left, Right: zero},
		Less{Left: zero, Right: right},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestIntegerSortedTernaryFunctionCongruence(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	z := IntegerVariable(3)
	function := DeclareIntTernaryFunction(4, "combine3")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		Not{Value: Equal{
			Left:  ApplySortedTernary(function, x, y, z),
			Right: ApplySortedTernary(function, y, x, z),
		}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedIntegerPredicateCongruence(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	predicate := DeclareIntPredicate(3, "p")
	formula := And{Values: []Term[BoolSort]{
		LessEqual{Left: x, Right: y},
		LessEqual{Left: y, Right: x},
		ApplySortedUnary(predicate, x),
		Not{Value: ApplySortedUnary(predicate, y)},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
	one := Integer{Value: 1}
	affine := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		ApplySortedUnary(predicate, Add{Values: []Term[IntSort]{x, one}}),
		Not{Value: ApplySortedUnary(predicate, Add{Values: []Term[IntSort]{y, one}})},
	}}
	if result := Check(Assert(2, New(), affine)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("affine result=%T", result)
	}
}

func TestSharedBinaryIntegerPredicateCongruence(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	z := IntegerVariable(3)
	predicate := DeclareIntBinaryPredicate(4, "p2")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		ApplySortedBinary(predicate, x, z),
		Not{Value: ApplySortedBinary(predicate, y, z)},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedIntegerEUFConditionalApplications(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	zero := Integer{Value: 0}
	function := DeclareIntUnaryFunction(3, "f")
	for name, condition := range map[string]Term[BoolSort]{
		"then": LessEqual{Left: x, Right: y},
		"else": Less{Left: x, Right: y},
	} {
		thenTerm, elseTerm := Term[IntSort](ApplySortedUnary(function, x)), Term[IntSort](zero)
		if name == "else" {
			thenTerm, elseTerm = zero, ApplySortedUnary(function, x)
		}
		conditional := If[IntSort]{
			Condition: condition, Then: thenTerm, Else: elseTerm,
		}
		formula := And{Values: []Term[BoolSort]{
			Equal{Left: x, Right: y},
			LessEqual{Left: conditional, Right: zero},
			Less{Left: zero, Right: ApplySortedUnary(function, y)},
		}}
		if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
			t.Fatalf("%s result=%T", name, result)
		}
	}
}

func TestCompactConditionalIntegerEUFSystem(t *testing.T) {
	system := CompactConditionalIntegerEUFSystem{
		Base: CompactIntegerEUFSystem{EqualityCount: 1, UnaryComparisonCount: 1},
		Conditional: IntegerConditionalComparison{
			Condition: IntegerDifferenceConstraint{
				PositiveID: 1, NegativeID: 2,
				HasPositive: true, HasNegative: true,
			},
			Then: IntegerConditionalBranch{
				Application: true, FunctionID: 3, ArgumentID: 1,
			},
			Else:  IntegerConditionalBranch{Constant: NewIntegerValue(0)},
			Bound: NewIntegerValue(0), ApplicationOnLeft: true,
		},
	}
	system.Base.EqualityLeft[0], system.Base.EqualityRight[0] = 1, 2
	system.Base.UnaryComparisons[0] = IntegerUnaryComparison{
		FunctionID: 3, ArgumentID: 2, Bound: NewIntegerValue(0),
		ApplicationOnLeft: false, Strict: true,
	}
	if result := Check(Assert(1, New(), system)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
	system.Base.EqualityCount = 0
	if result := Check(Assert(2, New(), system)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("satisfiable result=%T", result)
	}
}

func TestSharedIntegerEUFPropagatesApplicationEqualityIntoLIA(t *testing.T) {
	x := IntegerVariable(1)
	y := IntegerVariable(2)
	z := IntegerVariable(3)
	function := DeclareIntUnaryFunction(4, "f")
	application := ApplySortedUnary(function, z)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: application, Right: x},
		Equal{Left: application, Right: y},
		Less{Left: x, Right: y},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestCompactIntegerEUFSystem(t *testing.T) {
	system := CompactIntegerEUFSystem{
		EqualityCount: 1, BinaryComparisonCount: 2,
	}
	system.EqualityLeft[0], system.EqualityRight[0] = 1, 2
	system.BinaryComparisons[0] = IntegerBinaryComparison{
		FunctionID: 3, FirstArgumentID: 1, SecondArgumentID: 2,
		Bound: NewIntegerValue(0), ApplicationOnLeft: true,
	}
	system.BinaryComparisons[1] = IntegerBinaryComparison{
		FunctionID: 3, FirstArgumentID: 2, SecondArgumentID: 1,
		Bound: NewIntegerValue(0), ApplicationOnLeft: false, Strict: true,
	}
	if result := Check(Assert(1, New(), system)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
	system.BinaryComparisons[1].Strict = false
	if result := Check(Assert(2, New(), system)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("satisfiable result=%T", result)
	}
}

func TestCompactIntegerEUFTernarySystem(t *testing.T) {
	system := CompactIntegerEUFSystem{
		EqualityCount: 1, TernaryComparisonCount: 2,
	}
	system.EqualityLeft[0], system.EqualityRight[0] = 1, 2
	system.TernaryComparisons[0] = IntegerTernaryComparison{
		FunctionID: 4, FirstArgumentID: 1, SecondArgumentID: 2,
		ThirdArgumentID: 3, Bound: NewIntegerValue(0), ApplicationOnLeft: true,
	}
	system.TernaryComparisons[1] = IntegerTernaryComparison{
		FunctionID: 4, FirstArgumentID: 2, SecondArgumentID: 1,
		ThirdArgumentID: 3, Bound: NewIntegerValue(0),
		ApplicationOnLeft: false, Strict: true,
	}
	if result := Check(Assert(1, New(), system)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestCompactIntegerEUFSystemExchangesDifferenceEquality(t *testing.T) {
	system := CompactIntegerEUFSystem{DifferenceCount: 2, RelationCount: 1}
	system.Differences[0] = IntegerDifferenceConstraint{
		PositiveID: 1, NegativeID: 2, HasPositive: true, HasNegative: true,
	}
	system.Differences[1] = IntegerDifferenceConstraint{
		PositiveID: 2, NegativeID: 1, HasPositive: true, HasNegative: true,
	}
	system.Relations[0] = UninterpretedEUFRelation{
		Left: UninterpretedEUFTerm{
			Kind: 2, SortID: -2, FunctionID: 3, FirstSortID: -2, FirstID: 1,
		},
		Right: UninterpretedEUFTerm{
			Kind: 2, SortID: -2, FunctionID: 3, FirstSortID: -2, FirstID: 2,
		},
		Negated: true,
	}
	if result := Check(Assert(1, New(), system)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedRealPredicatesExchangeLRAEquality(t *testing.T) {
	x := RealSymbol{ID: 1}
	y := RealSymbol{ID: 2}
	z := RealSymbol{ID: 3}
	unary := DeclareRealPredicate(4, "p")
	binary := DeclareRealBinaryPredicate(5, "q")
	for name, formula := range map[string]Term[BoolSort]{
		"unary": And{Values: []Term[BoolSort]{
			RealLessEqual{Left: x, Right: y},
			RealLessEqual{Left: y, Right: x},
			ApplySortedUnary(unary, x),
			Not{Value: ApplySortedUnary(unary, y)},
		}},
		"binary": And{Values: []Term[BoolSort]{
			Equal{Left: x, Right: y},
			ApplySortedBinary(binary, x, z),
			Not{Value: ApplySortedBinary(binary, y, z)},
		}},
	} {
		if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
			t.Fatalf("%s result=%T", name, result)
		}
	}
}

func TestSharedRealTernaryFunctionArithmetic(t *testing.T) {
	x := RealSymbol{ID: 1}
	y := RealSymbol{ID: 2}
	z := RealSymbol{ID: 3}
	zero := Real{Value: NewRational(0, 1)}
	function := DeclareRealTernaryFunction(4, "combine3")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		RealLessEqual{
			Left: ApplySortedTernary(function, x, y, z), Right: zero,
		},
		RealLess{
			Left: zero, Right: ApplySortedTernary(function, y, x, z),
		},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestGroundIntegerRealCoercions(t *testing.T) {
	huge, err := ParseIntegerValue("123456789012345678901234567890")
	if err != nil {
		t.Fatal(err)
	}
	formula := And{Values: []Term[BoolSort]{
		Equal{
			Left:  IntToReal(IntegerTerm(huge)),
			Right: Real{Value: MustParseRational("123456789012345678901234567890")},
		},
		Equal{
			Left:  RealToInt(Real{Value: MustParseRational("-3/2")}),
			Right: Integer{Value: -2},
		},
		RealIsInt(Real{Value: MustParseRational("8/2")}),
		Not{Value: RealIsInt(Real{Value: MustParseRational("3/2")})},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSymbolicIntegerToRealComparisons(t *testing.T) {
	x := IntegerVariable(1)
	formula := And{Values: []Term[BoolSort]{
		RealLessEqual{
			Left:  Real{Value: MustParseRational("3/2")},
			Right: IntToReal(x),
		},
		RealLess{
			Left:  IntToReal(x),
			Right: Real{Value: MustParseRational("5/2")},
		},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, New(), formula)))
	}
	if value, found := IntegerModelValue(result.Value, x); !found || CompareIntegerValue(value, NewIntegerValue(2)) != 0 {
		t.Fatalf("x=%v found=%v", value, found)
	}

	fractionalEquality := Equal{
		Left:  IntToReal(x),
		Right: Real{Value: MustParseRational("3/2")},
	}
	if result := Check(Assert(2, New(), fractionalEquality)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("fractional equality result=%T", result)
	}
}

func TestSymbolicIntegerRealRoundTrips(t *testing.T) {
	x := IntegerVariable(1)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: RealToInt(IntToReal(x)), Right: x},
		RealIsInt(IntToReal(x)),
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
	if result := Check(Assert(2, New(), Not{Value: Equal{Left: RealToInt(IntToReal(x)), Right: x}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("negated round-trip result=%T", result)
	}
	if result := Check(Assert(3, New(), Not{Value: RealIsInt(IntToReal(x))})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("negated integrality result=%T", result)
	}
}

func TestAffineIntegerRealCoercions(t *testing.T) {
	x := IntegerVariable(1)
	xReal := IntToReal(x)
	fractional := RealAdd{Values: []Term[RealSort]{
		xReal,
		Real{Value: MustParseRational("3/2")},
	}}
	scaled := RealSubtract{
		Left: RealScale{
			Coefficient: NewRational(2, 1),
			Value:       xReal,
		},
		Right: Real{Value: MustParseRational("5/2")},
	}
	integral := RealAdd{Values: []Term[RealSort]{
		xReal,
		Real{Value: MustParseRational("4/2")},
	}}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: Integer{Value: 7}},
		Equal{Left: RealToInt(fractional), Right: Integer{Value: 8}},
		Equal{Left: RealToInt(scaled), Right: Integer{Value: 11}},
		Equal{Left: RealToInt(integral), Right: Integer{Value: 9}},
		Not{Value: RealIsInt(fractional)},
		Not{Value: RealIsInt(scaled)},
		RealIsInt(integral),
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestAffineIntegerRealComparisons(t *testing.T) {
	x, y := IntegerVariable(1), IntegerVariable(2)
	left := RealAdd{Values: []Term[RealSort]{
		IntToReal(x),
		Real{Value: MustParseRational("3/2")},
	}}
	right := RealAdd{Values: []Term[RealSort]{
		IntToReal(y),
		Real{Value: MustParseRational("1/2")},
	}}
	upper := RealAdd{Values: []Term[RealSort]{
		IntToReal(y),
		Real{Value: MustParseRational("1")},
	}}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: Integer{Value: 3}},
		Equal{Left: y, Right: Integer{Value: 4}},
		Equal{Left: left, Right: right},
		RealLess{Left: left, Right: upper},
		Not{Value: RealLess{Left: upper, Right: left}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestRationalScaledIntegerRealCoercions(t *testing.T) {
	x := IntegerVariable(1)
	scaled := RealScale{
		Coefficient: NewRational(3, 2),
		Value:       IntToReal(x),
	}
	nonIntegral := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: Integer{Value: 7}},
		Equal{Left: RealToInt(scaled), Right: Integer{Value: 10}},
		Not{Value: RealIsInt(scaled)},
	}}
	if result := Check(Assert(1, New(), nonIntegral)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("non-integral result=%T", result)
	}
	integral := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: Integer{Value: 8}},
		Equal{Left: RealToInt(scaled), Right: Integer{Value: 12}},
		RealIsInt(scaled),
	}}
	if result := Check(Assert(2, New(), integral)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("integral result=%T", result)
	}
	negative := RealScale{
		Coefficient: NewRational(-3, 2),
		Value:       IntToReal(x),
	}
	negativeFractional := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: Integer{Value: 7}},
		Equal{Left: RealToInt(negative), Right: Integer{Value: -11}},
		Not{Value: RealIsInt(negative)},
	}}
	if result := Check(Assert(3, New(), negativeFractional)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("negative fractional result=%T", result)
	}
}

func TestSharedRealEUFExchangesLRAImpliedEquality(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	function := DeclareRealUnaryFunction(3, "f")
	formula := And{Values: []Term[BoolSort]{
		RealLessEqual{Left: x, Right: y},
		RealLessEqual{Left: y, Right: x},
		Not{Value: Equal{Left: ApplySortedUnary(function, x), Right: ApplySortedUnary(function, y)}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedRealEUFUsesSimplexEntailmentForTransitiveEquality(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	z := RealSymbol{ID: 3, Name: "z"}
	function := DeclareRealUnaryFunction(4, "f")
	formula := And{Values: []Term[BoolSort]{
		RealLessEqual{Left: x, Right: z},
		RealLessEqual{Left: z, Right: x},
		RealLessEqual{Left: y, Right: z},
		RealLessEqual{Left: z, Right: y},
		Not{Value: Equal{Left: ApplySortedUnary(function, x), Right: ApplySortedUnary(function, y)}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedRealEUFPropagatesDerivedEqualityIntoLRA(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	z := RealSymbol{ID: 3, Name: "z"}
	function := DeclareRealUnaryFunction(4, "f")
	application := ApplySortedUnary(function, z)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: application, Right: x},
		Equal{Left: application, Right: y},
		RealLess{Left: x, Right: y},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedRealEUFSatisfiableDisequalityKeepsExactModel(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	function := DeclareRealUnaryFunction(3, "f")
	formula := And{Values: []Term[BoolSort]{
		RealLess{Left: x, Right: y},
		Not{Value: Equal{Left: ApplySortedUnary(function, x), Right: ApplySortedUnary(function, y)}},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, New(), formula)))
	}
	xValue, xOK := RealValue(result.Value, x)
	yValue, yOK := RealValue(result.Value, y)
	if !xOK || !yOK || rationalCmp(xValue, yValue) >= 0 {
		t.Fatalf("x=%s/%v y=%s/%v", xValue, xOK, yValue, yOK)
	}
}

func TestSharedRealEUFPurifiesApplicationsInsideArithmetic(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	function := DeclareRealUnaryFunction(3, "f")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		RealLessEqual{Left: ApplySortedUnary(function, x), Right: Real{Value: Rational{}}},
		RealLess{Left: Real{Value: Rational{}}, Right: ApplySortedUnary(function, y)},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedRealEUFPurifiesNonSymbolApplicationArguments(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	one := Real{Value: NewRational(1, 1)}
	function := DeclareRealUnaryFunction(3, "f")
	leftArgument := RealAdd{Values: []Term[RealSort]{x, one}}
	rightArgument := RealAdd{Values: []Term[RealSort]{y, one}}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		RealLessEqual{Left: ApplySortedUnary(function, leftArgument), Right: Real{Value: Rational{}}},
		RealLess{Left: Real{Value: Rational{}}, Right: ApplySortedUnary(function, rightArgument)},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestSharedRealEUFPurifiesBinaryApplications(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	u := RealSymbol{ID: 3, Name: "u"}
	v := RealSymbol{ID: 4, Name: "v"}
	function := DeclareRealBinaryFunction(8, "combine")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		Equal{Left: u, Right: v},
		RealLessEqual{Left: ApplySortedBinary(function, x, u), Right: Real{Value: Rational{}}},
		RealLess{Left: Real{Value: Rational{}}, Right: ApplySortedBinary(function, y, v)},
	}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("binary congruent applications under contradictory bounds should be unsatisfiable")
	}
}

func TestSharedRealEUFPurifiesBinaryAffineArguments(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	function := DeclareRealBinaryFunction(8, "combine")
	one := Real{Value: NewRational(1, 1)}
	left := ApplySortedBinary(function, RealAdd{Values: []Term[RealSort]{x, one}}, y)
	right := ApplySortedBinary(function, RealAdd{Values: []Term[RealSort]{y, one}}, x)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		RealLessEqual{Left: left, Right: Real{Value: Rational{}}},
		RealLess{Left: Real{Value: Rational{}}, Right: right},
	}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("binary applications with equal affine arguments should be unsatisfiable")
	}
}

func TestBitVectorBitBlastBooleanOperations(t *testing.T) {
	x := BitVecConst(8, 1, "x")
	value := BitVecVal(8, 0xa5)
	mask := BitVecVal(8, 0x0f)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: value},
		Not{Value: Equal{Left: BitVecAnd(x, mask), Right: BitVecVal(8, 0x05)}},
	}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("fixed symbol and masked value contradiction should be unsatisfiable")
	}
}

func TestBitVectorAdditionWrapsAtIndexedWidth(t *testing.T) {
	wrapped := BitVecAdd(BitVecVal(8, 255), BitVecVal(8, 1))
	formula := Not{Value: Equal{Left: wrapped, Right: BitVecVal(8, 0)}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("8-bit addition must wrap modulo 256")
	}
}

func TestArbitraryWidthBitVectorValue(t *testing.T) {
	value, err := ParseBitVector(130, "0x100000000000000000000000000000001")
	if err != nil {
		t.Fatal(err)
	}
	if value.Width() != 130 || !value.Bit(128) || !value.Bit(0) || value.Bit(129) {
		t.Fatalf("unexpected 130-bit value: width=%d bit128=%v bit0=%v", value.Width(), value.Bit(128), value.Bit(0))
	}
	formula := Not{Value: Equal{Left: bitVector[BitVecSort]{value: value}, Right: bitVector[BitVecSort]{value: value}}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("arbitrary-width value must equal itself")
	}
}

func TestBitVectorUnsignedAndSignedOrdering(t *testing.T) {
	unsignedFalse := BitVecULT(BitVecVal(8, 0xff), BitVecVal(8, 0))
	if _, ok := Check(Assert(1, New(), unsignedFalse)).(Unsatisfiable); !ok {
		t.Fatal("255 must not be unsigned-less than zero")
	}
	signedTrue := BitVecSLT(BitVecVal(8, 0xff), BitVecVal(8, 0))
	if _, ok := Check(Assert(2, New(), Not{Value: signedTrue})).(Unsatisfiable); !ok {
		t.Fatal("-1 must be signed-less than zero")
	}
	equal := BitVecULE(BitVecVal(8, 7), BitVecVal(8, 7))
	if _, ok := Check(Assert(3, New(), Not{Value: equal})).(Unsatisfiable); !ok {
		t.Fatal("unsigned <= must include equality")
	}
}

func TestBitVectorSubtractionAndMultiplicationWrap(t *testing.T) {
	underflow := BitVecSub(BitVecVal(8, 0), BitVecVal(8, 1))
	product := BitVecMul(BitVecVal(8, 25), BitVecVal(8, 12))
	formula := Or{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: underflow, Right: BitVecVal(8, 0xff)}},
		Not{Value: Equal{Left: product, Right: BitVecVal(8, 44)}},
	}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("subtraction and multiplication must wrap modulo indexed width")
	}
}

func TestBitVectorShiftBoundarySemantics(t *testing.T) {
	formula := Or{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: BitVecSHL(BitVecVal(5, 3), BitVecVal(5, 5)), Right: BitVecVal(5, 0)}},
		Not{Value: Equal{Left: BitVecLSHR(BitVecVal(5, 31), BitVecVal(5, 7)), Right: BitVecVal(5, 0)}},
		Not{Value: Equal{Left: BitVecASHR(BitVecVal(5, 0x10), BitVecVal(5, 7)), Right: BitVecVal(5, 0x1f)}},
		Not{Value: Equal{Left: BitVecSHL(BitVecVal(8, 3), BitVecVal(8, 2)), Right: BitVecVal(8, 12)}},
	}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("bit-vector shifts must honor full and out-of-range amounts")
	}
}

func TestBitVectorDivisionAndRemainderSemantics(t *testing.T) {
	formula := Or{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: BitVecUDiv(BitVecVal(8, 100), BitVecVal(8, 7)), Right: BitVecVal(8, 14)}},
		Not{Value: Equal{Left: BitVecURem(BitVecVal(8, 100), BitVecVal(8, 7)), Right: BitVecVal(8, 2)}},
		Not{Value: Equal{Left: BitVecUDiv(BitVecVal(8, 100), BitVecVal(8, 0)), Right: BitVecVal(8, 0xff)}},
		Not{Value: Equal{Left: BitVecURem(BitVecVal(8, 100), BitVecVal(8, 0)), Right: BitVecVal(8, 100)}},
		Not{Value: Equal{Left: BitVecSDiv(BitVecVal(8, 0x9c), BitVecVal(8, 7)), Right: BitVecVal(8, 0xf2)}},
		Not{Value: Equal{Left: BitVecSRem(BitVecVal(8, 0x9c), BitVecVal(8, 7)), Right: BitVecVal(8, 0xfe)}},
		Not{Value: Equal{Left: BitVecSDiv(BitVecVal(8, 0x80), BitVecVal(8, 0xff)), Right: BitVecVal(8, 0x80)}},
		Not{Value: Equal{Left: BitVecSDiv(BitVecVal(8, 0x80), BitVecVal(8, 0)), Right: BitVecVal(8, 1)}},
	}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("division and remainder must match SMT-LIB corner semantics")
	}
}

func TestBitVectorStructuralOperators(t *testing.T) {
	formula := Or{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: BitVecConcat(4, 4, BitVecVal(4, 0xa), BitVecVal(4, 0xb)), Right: BitVecVal(8, 0xab)}},
		Not{Value: Equal{Left: BitVecExtract(7, 4, BitVecVal(8, 0xab)), Right: BitVecVal(4, 0xa)}},
		Not{Value: Equal{Left: BitVecZeroExtend(8, BitVecVal(8, 0xff)), Right: BitVecVal(16, 0x00ff)}},
		Not{Value: Equal{Left: BitVecSignExtend(8, BitVecVal(8, 0xff)), Right: BitVecVal(16, 0xffff)}},
	}}
	if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("structural bit-vector operators must preserve indexed layouts")
	}
}

func TestBitVectorRotateRepeatOperators(t *testing.T) {
	x := BitVecConst(8, 1, "x")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: BitVecVal(8, 0x81)},
		Not{Value: Equal{Left: BitVecRotateLeft(1, x), Right: BitVecVal(8, 0x03)}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("rotation result=%T", result)
	}
	repeated := BitVecRepeat(2, BitVecVal(4, 0xa))
	if result := Check(Assert(2, New(), Not{Value: Equal{Left: repeated, Right: BitVecVal(8, 0xaa)}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("repeat result=%T", result)
	}
}

func TestArbitraryWidthBitVectorRotateRepeatValues(t *testing.T) {
	value, err := ParseBitVector(130, "0x200000000000000000000000000000000")
	if err != nil {
		t.Fatal(err)
	}
	left := RotateLeftBitVectorValue(value, 1)
	if !left.Bit(0) || left.Bit(129) {
		t.Fatalf("rotate-left width=%d low=%v high=%v", left.Width(), left.Bit(0), left.Bit(129))
	}
	if right := RotateRightBitVectorValue(left, 1); !EqualBitVectorValue(right, value) {
		t.Fatal("arbitrary-width rotations should be inverse")
	}
	nibble := NewBitVectorUint64(4, 0xa)
	repeated := RepeatBitVectorValue(nibble, 33)
	if repeated.Width() != 132 || !repeated.Bit(131) || repeated.Bit(128) {
		t.Fatalf("repeat width=%d high nibble=%v%v%v%v", repeated.Width(), repeated.Bit(131), repeated.Bit(130), repeated.Bit(129), repeated.Bit(128))
	}
}

func TestBitVectorOverflowPredicates(t *testing.T) {
	trueCases := []Term[BoolSort]{
		BitVecUAddOverflow(BitVecVal(8, 0xff), BitVecVal(8, 1)),
		BitVecSAddOverflow(BitVecVal(8, 0x7f), BitVecVal(8, 1)),
		BitVecUSubOverflow(BitVecVal(8, 0), BitVecVal(8, 1)),
		BitVecSSubOverflow(BitVecVal(8, 0x80), BitVecVal(8, 1)),
		BitVecUMulOverflow(BitVecVal(8, 0x10), BitVecVal(8, 0x10)),
		BitVecSMulOverflow(BitVecVal(8, 0x40), BitVecVal(8, 2)),
		BitVecSDivOverflow(BitVecVal(8, 0x80), BitVecVal(8, 0xff)),
		BitVecNegOverflow(BitVecVal(8, 0x80)),
	}
	for index, predicate := range trueCases {
		if result := Check(Assert(index+1, New(), Not{Value: predicate})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
			t.Fatalf("true predicate %d result=%T", index, result)
		}
	}
	falseCases := []Term[BoolSort]{
		BitVecUAddOverflow(BitVecVal(8, 1), BitVecVal(8, 2)),
		BitVecSAddOverflow(BitVecVal(8, 0xff), BitVecVal(8, 1)),
		BitVecUSubOverflow(BitVecVal(8, 2), BitVecVal(8, 1)),
		BitVecSSubOverflow(BitVecVal(8, 1), BitVecVal(8, 1)),
		BitVecUMulOverflow(BitVecVal(8, 3), BitVecVal(8, 4)),
		BitVecSMulOverflow(BitVecVal(8, 0xfe), BitVecVal(8, 2)),
		BitVecSDivOverflow(BitVecVal(8, 0x80), BitVecVal(8, 1)),
		BitVecNegOverflow(BitVecVal(8, 0x7f)),
	}
	for index, predicate := range falseCases {
		if result := Check(Assert(index+20, New(), predicate)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
			t.Fatalf("false predicate %d result=%T", index, result)
		}
	}
}

func TestArbitraryWidthBitVectorOverflowValues(t *testing.T) {
	maximum, err := ParseBitVector(130, "0x3ffffffffffffffffffffffffffffffff")
	if err != nil {
		t.Fatal(err)
	}
	one := NewBitVectorUint64(130, 1)
	if !UnsignedAddOverflowBitVectorValue(maximum, one) {
		t.Fatal("130-bit unsigned addition should overflow")
	}
	minimum := NewBitVectorUint64(130, 0)
	minimum.large = new(big.Int).Lsh(big.NewInt(1), 129)
	if !NegOverflowBitVectorValue(minimum) || !SignedDivOverflowBitVectorValue(minimum, NotBitVectorValue(NewBitVectorUint64(130, 0))) {
		t.Fatal("130-bit signed minimum boundary should overflow")
	}
}

func TestGroundBitVectorFunctionCongruence(t *testing.T) {
	x := BitVecConst(8, 1, "x")
	y := BitVecConst(8, 2, "y")
	function := DeclareBitVecUnaryFunction(8, 4, 3, "f")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		Not{Value: Equal{Left: ApplyBitVecUnary(function, x), Right: ApplyBitVecUnary(function, y)}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("unary congruence result=%T", result)
	}
	nested := Not{Value: Equal{
		Left:  ApplyBitVecUnary(function, BitVecZeroExtend(4, ApplyBitVecUnary(function, x))),
		Right: ApplyBitVecUnary(function, BitVecZeroExtend(4, ApplyBitVecUnary(function, y))),
	}}
	if result := Check(Assert(2, New(), And{Values: []Term[BoolSort]{Equal{Left: x, Right: y}, nested}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("nested congruence result=%T", result)
	}
}

func TestGroundBinaryBitVectorFunctionCongruenceAndModel(t *testing.T) {
	x := BitVecConst(8, 1, "x")
	y := BitVecConst(8, 2, "y")
	a := BitVecConst(4, 3, "a")
	b := BitVecConst(4, 4, "b")
	function := DeclareBitVecBinaryFunction(8, 4, 16, 5, "combine")
	left := ApplyBitVecBinary(function, x, a)
	right := ApplyBitVecBinary(function, y, b)
	formula := And{Values: []Term[BoolSort]{Equal{Left: x, Right: y}, Equal{Left: a, Right: b}, Not{Value: Equal{Left: left, Right: right}}}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("binary congruence result=%T", result)
	}
	sat, ok := Check(Assert(2, New(), And{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: x, Right: y}}, Equal{Left: left, Right: right},
	}})).(Satisfiable)
	if !ok {
		t.Fatal("bit-vector functions need not be injective")
	}
	leftValue, leftOK := BitVecModelValue(sat.Value, left)
	rightValue, rightOK := BitVecModelValue(sat.Value, right)
	if !leftOK || !rightOK || !EqualBitVectorValue(leftValue, rightValue) {
		t.Fatalf("application model left=%v/%v right=%v/%v", leftValue, leftOK, rightValue, rightOK)
	}
}

func TestSharedRealEUFPurifiedArithmeticCanRemainSatisfiable(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	function := DeclareRealUnaryFunction(3, "f")
	formula := And{Values: []Term[BoolSort]{
		RealLess{Left: x, Right: y},
		RealLessEqual{Left: ApplySortedUnary(function, x), Right: Real{Value: Rational{}}},
		RealLessEqual{Left: Real{Value: NewRational(1, 1)}, Right: ApplySortedUnary(function, y)},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestArbitraryPrecisionRationalNormalization(t *testing.T) {
	if got := NewRational(2, 4).String(); got != "1/2" {
		t.Fatalf("2/4=%s", got)
	}
	value := MustParseRational("123456789012345678901234567890.125")
	if got := value.String(); got != "987654312098765431209876543121/8" {
		t.Fatalf("parsed=%s", got)
	}
}

func TestHybridRationalAgreesWithBigRat(t *testing.T) {
	random := rand.New(rand.NewSource(31))
	for example := 0; example < 5000; example++ {
		integer := func() int64 {
			value := random.Int63()
			if random.Intn(2) == 0 {
				value = -value
			}
			return value
		}
		denominator := func() int64 {
			value := integer()
			if value == 0 {
				return 1
			}
			return value
		}
		leftNumerator, leftDenominator := integer(), denominator()
		rightNumerator, rightDenominator := integer(), denominator()
		left := NewRational(leftNumerator, leftDenominator)
		right := NewRational(rightNumerator, rightDenominator)
		leftBig := new(big.Rat).SetFrac(big.NewInt(leftNumerator), big.NewInt(leftDenominator))
		rightBig := new(big.Rat).SetFrac(big.NewInt(rightNumerator), big.NewInt(rightDenominator))
		checks := []struct {
			name string
			got  Rational
			want *big.Rat
		}{
			{"add", rationalAdd(left, right), new(big.Rat).Add(leftBig, rightBig)},
			{"subtract", rationalSub(left, right), new(big.Rat).Sub(leftBig, rightBig)},
			{"multiply", rationalMul(left, right), new(big.Rat).Mul(leftBig, rightBig)},
		}
		if rightNumerator != 0 {
			checks = append(checks, struct {
				name string
				got  Rational
				want *big.Rat
			}{"divide", rationalQuo(left, right), new(big.Rat).Quo(leftBig, rightBig)})
		}
		for _, check := range checks {
			if got, want := check.got.String(), check.want.RatString(); got != want {
				t.Fatalf("example %d %s: got %s want %s", example, check.name, got, want)
			}
		}
		if got, want := rationalCmp(left, right), leftBig.Cmp(rightBig); got != want {
			t.Fatalf("example %d compare: got %d want %d", example, got, want)
		}
	}
}

func TestExactLinearRealArithmeticModel(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	y := RealSymbol{ID: 2, Name: "y"}
	formula := And{Values: []Term[BoolSort]{
		RealLessEqual{Left: RealAdd{Values: []Term[RealSort]{x, y}}, Right: Real{Value: NewRational(3, 1)}},
		RealLessEqual{Left: Real{Value: NewRational(1, 2)}, Right: x},
		RealLess{Left: Real{Value: NewRational(1, 3)}, Right: y},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, New(), formula)))
	}
	xValue, xOK := RealValue(result.Value, x)
	yValue, yOK := RealValue(result.Value, y)
	if !xOK || !yOK || rationalCmp(xValue, NewRational(1, 2)) < 0 || rationalCmp(yValue, NewRational(1, 3)) <= 0 || rationalCmp(rationalAdd(xValue, yValue), NewRational(3, 1)) > 0 {
		t.Fatalf("model x=%s/%v y=%s/%v", xValue, xOK, yValue, yOK)
	}
}

func TestExactLinearRealArithmeticUnsat(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	formula := And{Values: []Term[BoolSort]{
		RealLess{Left: x, Right: Real{Value: Rational{}}},
		RealLessEqual{Left: Real{Value: Rational{}}, Right: x},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestStrictLinearRealUsesExactPositiveSlack(t *testing.T) {
	x := RealSymbol{ID: 1, Name: "x"}
	upper := MustParseRational("1/1000000000000000000000000000000000000000000")
	formula := And{Values: []Term[BoolSort]{
		RealLess{Left: Real{Value: Rational{}}, Right: x},
		RealLess{Left: x, Right: Real{Value: upper}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestExactLinearRealSimplexOverflowArenas(t *testing.T) {
	const variables = 10
	constraints := make([]Term[BoolSort], 0, variables*2)
	symbols := make([]Term[RealSort], variables)
	for index := 0; index < variables; index++ {
		symbol := RealSymbol{ID: index + 1, Name: "x"}
		symbols[index] = symbol
		value := Real{Value: NewRational(int64(index+1), 3)}
		constraints = append(constraints,
			RealLessEqual{Left: value, Right: symbol},
			RealLessEqual{Left: symbol, Right: value},
		)
	}
	result, ok := Check(Assert(1, New(), And{Values: constraints})).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, New(), And{Values: constraints})))
	}
	for index, symbol := range symbols {
		value, found := RealValue(result.Value, symbol)
		want := NewRational(int64(index+1), 3)
		if !found || rationalCmp(value, want) != 0 {
			t.Fatalf("x%d=%s/%v want %s", index+1, value, found, want)
		}
	}
}

func TestBitVectorIntegerConversions(t *testing.T) {
	x := BitVecConst(8, 1, "x")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: BitVecVal(8, 0xff)},
		Equal{Left: BitVecToNat(x), Right: Integer{Value: 255}},
		Equal{Left: BitVecToInt(x), Right: Integer{Value: -1}},
	}}
	result, ok := Check(Assert(1, New(), formula)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, New(), formula)))
	}
	unsigned, unsignedOK := ExactIntValue(result.Value, BitVecToNat(x))
	signed, signedOK := ExactIntValue(result.Value, BitVecToInt(x))
	if !unsignedOK || unsigned.String() != "255" || !signedOK || signed.String() != "-1" {
		t.Fatalf("unsigned=%s/%v signed=%s/%v", unsigned, unsignedOK, signed, signedOK)
	}

	for _, contradiction := range []Term[BoolSort]{
		Less{Left: BitVecToNat(x), Right: Integer{Value: 0}},
		LessEqual{Left: Integer{Value: 256}, Right: BitVecToNat(x)},
		Equal{Left: BitVecToInt(x), Right: Integer{Value: 128}},
	} {
		if _, ok := Check(Assert(2, New(), contradiction)).(Unsatisfiable); !ok {
			t.Fatalf("out-of-range comparison result=%T", Check(Assert(2, New(), contradiction)))
		}
	}
}

func TestWideBitVectorIntegerConversionsAndModels(t *testing.T) {
	wide, err := ParseBitVector(130, "0x3ffffffffffffffffffffffffffffffff")
	if err != nil {
		t.Fatal(err)
	}
	unsigned := BitVectorToIntegerValue(wide, false)
	signed := BitVectorToIntegerValue(wide, true)
	if unsigned.String() != "1361129467683753853853498429727072845823" || signed.String() != "-1" {
		t.Fatalf("unsigned=%s signed=%s", unsigned, signed)
	}
	model := Check(New()).(Satisfiable).Value
	unsignedModel, unsignedOK := ExactIntValue(model, BitVecToNat(BitVectorTerm(wide)))
	signedModel, signedOK := ExactIntValue(model, BitVecToInt(BitVectorTerm(wide)))
	if !unsignedOK || CompareIntegerValue(unsignedModel, unsigned) != 0 || !signedOK || CompareIntegerValue(signedModel, signed) != 0 {
		t.Fatalf("unsigned=%s/%v signed=%s/%v", unsignedModel, unsignedOK, signedModel, signedOK)
	}
}

func TestIntegerToBitVectorConversion(t *testing.T) {
	minusOne := IntToBitVec(8, Integer{Value: -1})
	model := Check(New()).(Satisfiable).Value
	value, ok := BitVecModelValue(model, minusOne)
	if !ok || !EqualBitVectorValue(value, NewBitVectorUint64(8, 0xff)) {
		t.Fatalf("value=%v/%v", value, ok)
	}

	x := IntSymbol{ID: 1, Name: "x"}
	result, sat := Check(Assert(1, New(), Equal{Left: x, Right: Integer{Value: -129}})).(Satisfiable)
	if !sat {
		t.Fatalf("integer result=%T", Check(Assert(1, New(), Equal{Left: x, Right: Integer{Value: -129}})))
	}
	value, ok = BitVecModelValue(result.Value, IntToBitVec(8, x))
	if !ok || !EqualBitVectorValue(value, NewBitVectorUint64(8, 0x7f)) {
		t.Fatalf("symbolic value=%v/%v", value, ok)
	}

	roundTrip := IntToBitVec(16, BitVecToInt(BitVecVal(8, 0x80)))
	value, ok = BitVecModelValue(model, roundTrip)
	if !ok || !EqualBitVectorValue(value, NewBitVectorUint64(16, 0xff80)) {
		t.Fatalf("round-trip=%v/%v", value, ok)
	}
}

func TestGroundArrayReadOverWrite(t *testing.T) {
	base := ConstArray[IntSort, IntSort](Integer{Value: 0})
	updated := Store(base, Integer{Value: 7}, Integer{Value: 42})
	nested := Store(updated, Integer{Value: 8}, Integer{Value: 99})
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: Select(updated, Integer{Value: 7}), Right: Integer{Value: 42}},
		Equal{Left: Select(updated, Integer{Value: 8}), Right: Integer{Value: 0}},
		Equal{Left: Select(nested, Integer{Value: 7}), Right: Integer{Value: 42}},
		Equal{Left: Select(nested, Integer{Value: 8}), Right: Integer{Value: 99}},
		Equal{Left: base, Right: ConstArray[IntSort, IntSort](Integer{Value: 0})},
		Equal{Left: nested, Right: Store(Store(ConstArray[IntSort, IntSort](Integer{Value: 0}), Integer{Value: 7}, Integer{Value: 42}), Integer{Value: 8}, Integer{Value: 99})},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
	contradiction := Not{Value: Equal{Left: Select(updated, Integer{Value: 7}), Right: Integer{Value: 42}}}
	if result := Check(Assert(2, New(), contradiction)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("contradiction=%#v", result)
	}
}

func TestGroundArraySelectCongruence(t *testing.T) {
	a := ArrayConst[IntSort, IntSort](1, "a")
	b := ArrayConst[IntSort, IntSort](2, "b")
	index := Integer{Value: 7}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: a, Right: b},
		Not{Value: Equal{Left: Select(a, index), Right: Select(b, index)}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("congruence=%#v", result)
	}

	valueConflict := And{Values: []Term[BoolSort]{
		Equal{Left: Select(a, index), Right: Integer{Value: 42}},
		Not{Value: Equal{Left: Select(a, index), Right: Integer{Value: 42}}},
	}}
	if result := Check(Assert(2, New(), valueConflict)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("value conflict=%#v", result)
	}

	if result := Check(Assert(3, New(), Not{Value: Equal{Left: a, Right: b}})); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("array disequality=%#v", result)
	}
}

func TestGroundArraySymbolicIndexCongruence(t *testing.T) {
	a := ArrayConst[IntSort, IntSort](1, "a")
	b := ArrayConst[IntSort, IntSort](2, "b")
	i := IntSymbol{ID: 11, Name: "i"}
	j := IntSymbol{ID: 12, Name: "j"}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: i, Right: j},
		Not{Value: Equal{Left: Select(Store(a, i, Integer{Value: 42}), j), Right: Integer{Value: 42}}},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("store/select=%#v", result)
	}

	arrayFormula := And{Values: []Term[BoolSort]{
		Equal{Left: a, Right: b}, Equal{Left: i, Right: j},
		Not{Value: Equal{Left: Select(a, i), Right: Select(b, j)}},
	}}
	if result := Check(Assert(2, New(), arrayFormula)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("array/index congruence=%#v", result)
	}
}

func TestGroundIntegerArrayExtensionalModel(t *testing.T) {
	a := ArrayConst[IntSort, IntSort](31, "a")
	b := ArrayConst[IntSort, IntSort](32, "b")
	seven := NewIntegerValue(7)
	eight := NewIntegerValue(8)
	formula := And{Values: []Term[BoolSort]{
		Not{Value: Equal{Left: a, Right: b}},
		Equal{Left: Select(a, IntegerTerm(seven)), Right: Integer{Value: 42}},
	}}
	result := Check(Assert(4, New(), formula))
	sat, ok := result.(Satisfiable)
	if !ok {
		t.Fatalf("result=%#v", result)
	}
	read, ok := IntegerArrayValue(sat.Value, a, seven)
	if !ok || CompareIntegerValue(read, NewIntegerValue(42)) != 0 {
		t.Fatalf("a[7]=%v, %v", read, ok)
	}
	aWitness, aOK := IntegerArrayValue(sat.Value, a, eight)
	bWitness, bOK := IntegerArrayValue(sat.Value, b, eight)
	if !aOK || !bOK || CompareIntegerValue(aWitness, bWitness) == 0 {
		t.Fatalf("missing extensional witness: a[8]=%v b[8]=%v", aWitness, bWitness)
	}
	stored := Store(a, IntegerTerm(eight), Integer{Value: 99})
	storedValue, ok := IntegerArrayValue(sat.Value, stored, eight)
	if !ok || CompareIntegerValue(storedValue, NewIntegerValue(99)) != 0 {
		t.Fatalf("store model=%v, %v", storedValue, ok)
	}
}

func TestGroundIntegerArrayStoreExtensionality(t *testing.T) {
	a := ArrayConst[IntSort, IntSort](41, "a")
	seven := Integer{Value: 7}
	eight := Integer{Value: 8}
	identity := Store(a, seven, Select(a, seven))
	if result := Check(Assert(1, New(), Not{Value: Equal{Left: identity, Right: a}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("store identity=%#v", result)
	}

	overwritten := Store(Store(a, seven, Integer{Value: 1}), seven, Integer{Value: 2})
	canonical := Store(a, seven, Integer{Value: 2})
	if result := Check(Assert(2, New(), Not{Value: Equal{Left: overwritten, Right: canonical}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("overwrite=%#v", result)
	}

	left := Store(Store(a, seven, Integer{Value: 1}), eight, Integer{Value: 2})
	right := Store(Store(a, eight, Integer{Value: 2}), seven, Integer{Value: 1})
	if result := Check(Assert(3, New(), Not{Value: Equal{Left: left, Right: right}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("commuting stores=%#v", result)
	}

	different := Not{Value: Equal{Left: Store(a, seven, Integer{Value: 1}), Right: Store(a, seven, Integer{Value: 2})}}
	if result := Check(Assert(4, New(), different)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("different stores=%#v", result)
	}
	if result := Check(Assert(5, New(), Equal{Left: Store(a, seven, Integer{Value: 1}), Right: Store(a, seven, Integer{Value: 2})})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("unequal stores equated=%#v", result)
	}
}

func TestGroundIntegerArrayCrossBaseStoreEquality(t *testing.T) {
	a := ArrayConst[IntSort, IntSort](51, "a")
	b := ArrayConst[IntSort, IntSort](52, "b")
	seven, eight := Integer{Value: 7}, Integer{Value: 8}
	left := Store(a, seven, Integer{Value: 1})
	right := Store(b, seven, Integer{Value: 1})
	outsideConflict := And{Values: []Term[BoolSort]{
		Equal{Left: left, Right: right},
		Not{Value: Equal{Left: Select(a, eight), Right: Select(b, eight)}},
	}}
	if result := Check(Assert(1, New(), outsideConflict)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("outside bridge=%#v", result)
	}

	overwrittenBases := And{Values: []Term[BoolSort]{
		Equal{Left: left, Right: right},
		Equal{Left: Select(a, seven), Right: Integer{Value: 2}},
		Equal{Left: Select(b, seven), Right: Integer{Value: 3}},
	}}
	result := Check(Assert(2, New(), overwrittenBases))
	sat, ok := result.(Satisfiable)
	if !ok {
		t.Fatalf("overwritten bases=%#v", result)
	}
	aOutside, aOK := IntegerArrayValue(sat.Value, a, NewIntegerValue(8))
	bOutside, bOK := IntegerArrayValue(sat.Value, b, NewIntegerValue(8))
	if !aOK || !bOK || CompareIntegerValue(aOutside, bOutside) != 0 {
		t.Fatalf("model bridge a[8]=%v/%v b[8]=%v/%v", aOutside, aOK, bOutside, bOK)
	}

	storeToSymbol := And{Values: []Term[BoolSort]{
		Equal{Left: left, Right: b},
		Not{Value: Equal{Left: Select(b, seven), Right: Integer{Value: 1}}},
	}}
	if result := Check(Assert(3, New(), storeToSymbol)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("store-to-symbol=%#v", result)
	}
}

func TestGroundIntegerArrayConstantBaseEquality(t *testing.T) {
	a := ArrayConst[IntSort, IntSort](61, "a")
	zero := ConstArray[IntSort, IntSort](Integer{Value: 0})
	one := ConstArray[IntSort, IntSort](Integer{Value: 1})
	seven, eight := Integer{Value: 7}, Integer{Value: 8}
	readConflict := And{Values: []Term[BoolSort]{
		Equal{Left: a, Right: zero},
		Not{Value: Equal{Left: Select(a, eight), Right: Integer{Value: 0}}},
	}}
	if result := Check(Assert(1, New(), readConflict)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("constant default=%#v", result)
	}
	if result := Check(Assert(2, New(), And{Values: []Term[BoolSort]{Equal{Left: a, Right: zero}, Not{Value: Equal{Left: a, Right: zero}}}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("constant contradiction=%#v", result)
	}
	if result := Check(Assert(3, New(), And{Values: []Term[BoolSort]{Equal{Left: a, Right: zero}, Equal{Left: a, Right: one}}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("conflicting defaults=%#v", result)
	}

	storedSymbol := Store(a, seven, Integer{Value: 0})
	storedConstant := Store(zero, seven, Integer{Value: 0})
	overwritten := And{Values: []Term[BoolSort]{
		Equal{Left: storedSymbol, Right: storedConstant},
		Equal{Left: Select(a, seven), Right: Integer{Value: 5}},
	}}
	result := Check(Assert(4, New(), overwritten))
	sat, ok := result.(Satisfiable)
	if !ok {
		t.Fatalf("overwritten base=%#v", result)
	}
	outside, outsideOK := IntegerArrayValue(sat.Value, a, NewIntegerValue(8))
	if !outsideOK || CompareIntegerValue(outside, NewIntegerValue(0)) != 0 {
		t.Fatalf("constant model a[8]=%v/%v", outside, outsideOK)
	}
	if result := Check(Assert(5, New(), Equal{Left: Store(a, seven, Integer{Value: 1}), Right: zero})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("visible store conflict=%#v", result)
	}
}

func TestMixedArrayArithmeticTheoryProduct(t *testing.T) {
	a := ArrayConst[IntSort, IntSort](71, "a")
	arrayLaw := Equal{Left: Select(Store(a, Integer{Value: 7}, Integer{Value: 42}), Integer{Value: 7}), Right: Integer{Value: 42}}
	x := IntSymbol{ID: 81, Name: "x"}
	y := IntSymbol{ID: 82, Name: "y"}
	formula := And{Values: []Term[BoolSort]{arrayLaw, LessEqual{Left: Subtract{Left: x, Right: y}, Right: Integer{Value: 3}}, LessEqual{Left: y, Right: Integer{Value: 2}}}}
	result := Check(Assert(1, New(), formula))
	sat, ok := result.(Satisfiable)
	if !ok {
		t.Fatalf("array+IDL=%#v", result)
	}
	xValue, xOK := ExactIntValue(sat.Value, x)
	yValue, yOK := ExactIntValue(sat.Value, y)
	if !xOK || !yOK || CompareIntegerValue(SubIntegerValue(xValue, yValue), NewIntegerValue(3)) > 0 || CompareIntegerValue(yValue, NewIntegerValue(2)) > 0 {
		t.Fatalf("IDL model x=%v/%v y=%v/%v", xValue, xOK, yValue, yOK)
	}
	bvConflict := Not{Value: Equal{Left: BitVecVal(8, 0xa5), Right: BitVecVal(8, 0xa5)}}
	if result := Check(Assert(2, New(), And{Values: []Term[BoolSort]{arrayLaw, bvConflict}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("array+BV=%#v", result)
	}
}

func TestMixedArraySharedIndexExchange(t *testing.T) {
	a := ArrayConst[IntSort, IntSort](72, "a")
	i := IntSymbol{ID: 91, Name: "i"}
	j := IntSymbol{ID: 92, Name: "j"}
	value := Integer{Value: 42}
	readConflict := Not{Value: Equal{Left: Select(Store(a, i, value), j), Right: value}}
	equalBounds := And{Values: []Term[BoolSort]{LessEqual{Left: i, Right: j}, LessEqual{Left: j, Right: i}, readConflict}}
	if result := Check(Assert(1, New(), equalBounds)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("implied index equality=%#v", result)
	}
	strictBounds := And{Values: []Term[BoolSort]{Less{Left: i, Right: j}, readConflict}}
	result := Check(Assert(2, New(), strictBounds))
	sat, ok := result.(Satisfiable)
	if !ok {
		t.Fatalf("distinct indices=%#v", result)
	}
	iValue, iOK := ExactIntValue(sat.Value, i)
	jValue, jOK := ExactIntValue(sat.Value, j)
	if !iOK || !jOK || CompareIntegerValue(iValue, jValue) >= 0 {
		t.Fatalf("shared model i=%v/%v j=%v/%v", iValue, iOK, jValue, jOK)
	}
}

func TestGroundBitVectorArrayReadOverWrite(t *testing.T) {
	base := ConstArray[BitVecSort, BitVecSort](BitVecVal(8, 0))
	index := BitVecVal(4, 3)
	other := BitVecVal(4, 4)
	value := BitVecVal(8, 0xa5)
	updated := Store(base, index, value)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: Select(updated, index), Right: value},
		Equal{Left: Select(updated, other), Right: BitVecVal(8, 0)},
	}}
	if result := Check(Assert(1, New(), formula)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
	if result := Check(Assert(2, New(), Not{Value: Equal{Left: Select(updated, index), Right: value}})); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("contradiction=%#v", result)
	}
}

func TestGroundBitVectorArrayCompactSymbolicIndex(t *testing.T) {
	array := ArrayConst[BitVecSort, BitVecSort](1, "memory")
	left := bitVectorSymbol[BitVecSort]{width: 4, iD: 2}
	right := bitVectorSymbol[BitVecSort]{width: 4, iD: 3}
	value := BitVectorTerm(NewBitVectorUint64(8, 0xa5))
	read := Equal{Left: Select(Store(array, left, value), right), Right: value}
	formula := BooleanConjunction{Count: 2}
	formula.InlineTerms[0] = BitVectorEUFRelation{
		Left: BitVectorEUFTerm{Kind: 1, Width: 4, SymbolID: 2}, Right: BitVectorEUFTerm{Kind: 1, Width: 4, SymbolID: 3},
	}
	formula.InlineTerms[1], formula.InlineNegated[1] = read, true
	if outcome, recognized := solveSharedArrayBitVector([]Term[BoolSort]{formula}); !recognized || outcome.status != checkUnsat {
		t.Fatalf("outcome=%#v", outcome)
	}
}

func TestGroundBitVectorArrayExtensionalModel(t *testing.T) {
	left := BitVectorArrayConst(4, 8, 1, "left")
	right := BitVectorArrayConst(4, 8, 2, "right")
	solver := Assert(1, New(), Not{Value: Equal{Left: left, Right: right}})
	result, ok := Check(solver).(Satisfiable)
	if !ok {
		t.Fatalf("result=%#v", Check(solver))
	}
	index := NewBitVectorUint64(4, 0)
	leftValue, leftOK := BitVectorArrayValue(result.Value, left, index)
	rightValue, rightOK := BitVectorArrayValue(result.Value, right, index)
	if !leftOK || !rightOK || EqualBitVectorValue(leftValue, rightValue) {
		t.Fatalf("left=%#v/%v right=%#v/%v", leftValue, leftOK, rightValue, rightOK)
	}
	stored := Store(left, BitVectorTerm(NewBitVectorUint64(4, 3)), BitVectorTerm(NewBitVectorUint64(8, 0xa5)))
	storedValue, storedOK := BitVectorArrayValue(result.Value, stored, NewBitVectorUint64(4, 3))
	if !storedOK || !EqualBitVectorValue(storedValue, NewBitVectorUint64(8, 0xa5)) {
		t.Fatalf("stored=%#v/%v", storedValue, storedOK)
	}
}

func BenchmarkGroundEUFCold(b *testing.B) {
	a := UninterpretedConstant(1, 1, "a")
	c := UninterpretedConstant(1, 2, "b")
	f := DeclareUnaryFunction(1, 1, 1, "f")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: a, Right: c},
		Not{Value: Equal{Left: ApplyUnary(f, a), Right: ApplyUnary(f, c)}},
	}}
	b.ReportAllocs()
	for b.Loop() {
		if _, ok := Check(Assert(1, New(), formula)).(Unsatisfiable); !ok {
			b.Fatal("unexpected result")
		}
	}
}

func BenchmarkCDCLPigeonholeCold(b *testing.B) {
	const pigeons, holes = 5, 4
	clauses := pigeonholeCNF(pigeons, holes)
	b.ReportAllocs()
	for b.Loop() {
		solver, ok := watchedSolverForTest(pigeons*holes, clauses)
		if !ok || solver.search() {
			b.Fatal("unexpected pigeonhole result")
		}
	}
}

func BenchmarkCDCLPigeonholeHardCold(b *testing.B) {
	const pigeons, holes = 7, 6
	clauses := pigeonholeCNF(pigeons, holes)
	b.ReportAllocs()
	for b.Loop() {
		solver, ok := watchedSolverForTest(pigeons*holes, clauses)
		if !ok || solver.search() {
			b.Fatal("unexpected pigeonhole result")
		}
	}
}
