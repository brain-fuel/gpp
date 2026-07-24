package smt

import "testing"

func TestFloatingPointBitVectorTermFromComponents(t *testing.T) {
	term := FloatingPointBitVectorTermFromComponents(
		8, 24,
		BitVectorTerm(NewBitVectorUint64(1, 0)),
		BitVectorTerm(NewBitVectorUint64(8, 0x7f)),
		BitVectorTerm(NewBitVectorUint64(23, 0)),
	)
	solver := Assert(1, New(), Equal{
		Left: term, Right: BitVectorTerm(NewBitVectorUint64(32, 0x3f800000)),
	})
	result := Check(solver)
	if _, ok := result.(Satisfiable); !ok {
		t.Fatalf("native floating-point constructor result=%T, want satisfiable", result)
	}
}

func TestSymbolicFloatingPointClassificationModels(t *testing.T) {
	tests := []struct {
		name     string
		relation Term[BoolSort]
		validate func(FloatingPointValue) bool
	}{
		{"NaN", FloatingPointNaNRelation(8, 24, 1), FloatingPointIsNaN},
		{"infinite", FloatingPointInfiniteRelation(8, 24, 1), FloatingPointIsInfinite},
		{"zero", FloatingPointZeroRelation(8, 24, 1), FloatingPointIsZero},
		{"subnormal", FloatingPointSubnormalRelation(8, 24, 1), FloatingPointIsSubnormal},
		{"normal", FloatingPointNormalRelation(8, 24, 1), FloatingPointIsNormal},
		{"negative", FloatingPointNegativeRelation(8, 24, 1), FloatingPointIsNegative},
		{"positive", FloatingPointPositiveRelation(8, 24, 1), FloatingPointIsPositive},
	}
	for index, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			result, ok := Check(Assert(index+1, New(), test.relation)).(Satisfiable)
			if !ok {
				t.Fatalf("result=%T", Check(Assert(index+1, New(), test.relation)))
			}
			bits, found := FloatingPointSymbolModelBits(result.Value, 1)
			if !found || bits.Width() != 32 {
				t.Fatalf("model bits=%#v/%v", bits, found)
			}
			if value := FloatingPointFromBits(8, 24, bits); !test.validate(value) {
				t.Fatalf("model bits %#v do not satisfy %s", bits, test.name)
			}
		})
	}
}

func TestFloatingPointPredicateBitVectorTerms(t *testing.T) {
	tests := []struct {
		predicate uint8
		bits      uint64
	}{
		{FloatingPointPredicateNaN, 0x7fc12345},
		{FloatingPointPredicateInfinite, 0xff800000},
		{FloatingPointPredicateZero, 0x80000000},
		{FloatingPointPredicateSubnormal, 0x00000001},
		{FloatingPointPredicateNormal, 0x3f800000},
		{FloatingPointPredicateNegative, 0xbf800000},
		{FloatingPointPredicatePositive, 0x3f800000},
	}
	for _, test := range tests {
		bits := NewBitVectorUint64(32, test.bits)
		term := FloatingPointPredicateBitVectorTerm(
			8, 24, BitVectorTerm(bits), test.predicate,
		)
		if _, ok := Check(Assert(1, New(), term)).(Satisfiable); !ok {
			t.Fatalf("predicate %d rejected %#x", test.predicate, test.bits)
		}
	}
}

func TestFloatingPointEqualityAndOrderBitVectorTerms(t *testing.T) {
	positiveZero := BitVectorTerm(NewBitVectorUint64(32, 0))
	negativeZero := BitVectorTerm(NewBitVectorUint64(32, 0x80000000))
	negativeOne := BitVectorTerm(NewBitVectorUint64(32, 0xbf800000))
	positiveOne := BitVectorTerm(NewBitVectorUint64(32, 0x3f800000))
	nan := BitVectorTerm(NewBitVectorUint64(32, 0x7fc12345))
	laws := []Term[BoolSort]{
		FloatingPointEqualBitVectorTerms(8, 24, positiveZero, negativeZero),
		FloatingPointComparisonBitVectorTerms(
			8, 24, negativeOne, positiveOne, FloatingPointComparisonLess,
		),
		FloatingPointComparisonBitVectorTerms(
			8, 24, negativeOne, positiveOne, FloatingPointComparisonLessOrEqual,
		),
		Not{Value: FloatingPointEqualBitVectorTerms(8, 24, nan, nan)},
		Not{Value: FloatingPointComparisonBitVectorTerms(
			8, 24, nan, positiveOne, FloatingPointComparisonLess,
		)},
	}
	if _, ok := Check(Assert(1, New(), And{Values: laws})).(Satisfiable); !ok {
		t.Fatal("arbitrary-term floating-point equality/order laws must be satisfiable")
	}
}

func TestFloatingPointUnaryBitVectorTerms(t *testing.T) {
	source := BitVectorTerm(NewBitVectorUint64(32, 0xbfc12345))
	absolute := FloatingPointAbsBitVectorTerm(8, 24, source)
	negated := FloatingPointNegBitVectorTerm(8, 24, source)
	expected := BitVectorTerm(NewBitVectorUint64(32, 0x3fc12345))
	laws := And{Values: []Term[BoolSort]{
		Equal{Left: absolute, Right: expected},
		Equal{Left: negated, Right: expected},
	}}
	if _, ok := Check(Assert(1, New(), laws)).(Satisfiable); !ok {
		t.Fatal("arbitrary-term floating-point unary laws must be satisfiable")
	}
}

func TestNegatedSymbolicFloatingPointClassification(t *testing.T) {
	relation := NewFloatingPointRelation(8, 24, 1, FloatingPointPredicateNaN)
	relation.Negated = true
	result, ok := Check(Assert(1, New(), relation)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, New(), relation)))
	}
	bits, found := FloatingPointSymbolModelBits(result.Value, 1)
	if !found || FloatingPointIsNaN(FloatingPointFromBits(8, 24, bits)) {
		t.Fatalf("negated NaN model=%#v/%v", bits, found)
	}
}

func TestCompactFloatingPointComparisonWithAssignedSymbols(t *testing.T) {
	solver := New()
	solver = Assert(1, solver, BitVectorRelation{
		Width: 32, SymbolID: 1, Value: NewBitVectorUint64(32, 0xbf800000),
	})
	solver = Assert(2, solver, BitVectorRelation{
		Width: 32, SymbolID: 2, Value: NewBitVectorUint64(32, 0x3f800000),
	})
	solver = AssertFloatingPointComparisonRelation(
		3, solver,
		NewFloatingPointComparisonRelation(
			8, 24, 1, 2, FloatingPointComparisonLess,
		),
	)
	result, ok := Check(solver).(Satisfiable)
	if !ok {
		t.Fatalf("expected satisfiable comparison, got %#v", Check(solver))
	}
	left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
	right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
	leftBits, leftInline := left.Uint64()
	rightBits, rightInline := right.Uint64()
	if !leftFound || !rightFound || !leftInline || !rightInline ||
		leftBits != 0xbf800000 || rightBits != 0x3f800000 {
		t.Fatalf("unexpected comparison model: left=%#x right=%#x", leftBits, rightBits)
	}
}

func TestFloatingPointComparisonBitBlastFallback(t *testing.T) {
	relation := NewFloatingPointComparisonRelation(
		8, 24, 1, 2, FloatingPointComparisonLessOrEqual,
	)
	result, ok := Check(AssertFloatingPointComparisonRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("unconstrained fp.leq must be satisfiable")
	}
	leftBits, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
	rightBits, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
	if !leftFound || !rightFound {
		t.Fatal("bit-blasted comparison must model both operands")
	}
	left := FloatingPointFromBits(8, 24, leftBits)
	right := FloatingPointFromBits(8, 24, rightBits)
	if !FloatingPointLessOrEqual(left, right) {
		t.Fatalf("invalid fp.leq model: left=%v right=%v", leftBits, rightBits)
	}
}

func TestUnconstrainedFloatingPointComparisonCanonicalModels(t *testing.T) {
	tests := []struct {
		name       string
		comparison uint8
		negated    bool
		same       bool
		wantUnsat  bool
	}{
		{"less", FloatingPointComparisonLess, false, false, false},
		{"not less", FloatingPointComparisonLess, true, false, false},
		{"less or equal", FloatingPointComparisonLessOrEqual, false, false, false},
		{"not less or equal", FloatingPointComparisonLessOrEqual, true, false, false},
		{"same less", FloatingPointComparisonLess, false, true, true},
		{"same not less", FloatingPointComparisonLess, true, true, false},
		{"same less or equal", FloatingPointComparisonLessOrEqual, false, true, false},
		{"same not less or equal", FloatingPointComparisonLessOrEqual, true, true, false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			rightID := 2
			if test.same {
				rightID = 1
			}
			relation := NewFloatingPointComparisonRelation(
				15, 113, 1, rightID, test.comparison,
			)
			relation.Negated = test.negated
			result := Check(AssertFloatingPointComparisonRelation(
				1, New(), relation,
			))
			if test.wantUnsat {
				if _, ok := result.(Unsatisfiable); !ok {
					t.Fatalf("result=%T, want unsatisfiable", result)
				}
				return
			}
			sat, ok := result.(Satisfiable)
			if !ok {
				t.Fatalf("result=%T, want satisfiable", result)
			}
			leftBits, leftFound := FloatingPointSymbolModelBits(
				sat.Value, 1,
			)
			rightBits, rightFound := FloatingPointSymbolModelBits(
				sat.Value, rightID,
			)
			if !leftFound || !rightFound ||
				leftBits.Width() != 128 || rightBits.Width() != 128 {
				t.Fatal("canonical comparison model is incomplete")
			}
			left := FloatingPointFromBits(15, 113, leftBits)
			right := FloatingPointFromBits(15, 113, rightBits)
			holds := FloatingPointLessThan(left, right)
			if test.comparison == FloatingPointComparisonLessOrEqual {
				holds = FloatingPointLessOrEqual(left, right)
			}
			if holds == test.negated {
				t.Fatalf("model does not satisfy comparison")
			}
		})
	}
}

func TestUnconstrainedFloatingPointEqualityCanonicalModels(t *testing.T) {
	for _, test := range []struct {
		name    string
		negated bool
		same    bool
	}{
		{"equal", false, false},
		{"not equal", true, false},
		{"self equal", false, true},
		{"self not equal through NaN", true, true},
	} {
		t.Run(test.name, func(t *testing.T) {
			rightID := 2
			if test.same {
				rightID = 1
			}
			relation := NewFloatingPointEqualityRelation(15, 113, 1, rightID)
			relation.Negated = test.negated
			result, ok := Check(AssertFloatingPointEqualityRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatal("expected satisfiable binary128 equality")
			}
			leftBits, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
			rightBits, rightFound := FloatingPointSymbolModelBits(result.Value, rightID)
			if !leftFound || !rightFound ||
				leftBits.Width() != 128 || rightBits.Width() != 128 {
				t.Fatal("canonical equality model is incomplete")
			}
			holds := FloatingPointEqual(
				FloatingPointFromBits(15, 113, leftBits),
				FloatingPointFromBits(15, 113, rightBits),
			)
			if holds == test.negated {
				t.Fatal("model does not satisfy equality polarity")
			}
		})
	}
}

func TestTwoIndependentFloatingPointEqualities(t *testing.T) {
	first := NewFloatingPointEqualityRelation(8, 24, 1, 2)
	second := NewFloatingPointEqualityRelation(8, 24, 3, 4)
	second.Negated = true
	solver := AssertFloatingPointEqualityRelation(1, New(), first)
	solver = AssertFloatingPointEqualityRelation(2, solver, second)
	result, ok := Check(solver).(Satisfiable)
	if !ok {
		t.Fatal("expected paired independent equality model")
	}
	for _, relation := range []FloatingPointEqualityRelation{first, second} {
		left, leftFound := FloatingPointSymbolModelBits(
			result.Value, relation.LeftSymbolID,
		)
		right, rightFound := FloatingPointSymbolModelBits(
			result.Value, relation.RightSymbolID,
		)
		if !leftFound || !rightFound {
			t.Fatal("paired equality model is incomplete")
		}
		holds := FloatingPointEqual(
			FloatingPointFromBits(8, 24, left),
			FloatingPointFromBits(8, 24, right),
		)
		if holds == relation.Negated {
			t.Fatal("paired equality model has wrong polarity")
		}
	}
}

func TestSharedFloatingPointEqualityGraph(t *testing.T) {
	equal12 := NewFloatingPointEqualityRelation(15, 113, 1, 2)
	distinct23 := NewFloatingPointEqualityRelation(15, 113, 2, 3)
	distinct23.Negated = true
	nanSelf := NewFloatingPointEqualityRelation(15, 113, 4, 4)
	nanSelf.Negated = true
	var compactAssignments [4]compactBitVectorAssignment
	compactAssignmentCount := 0
	if unsatisfiable, synthesized := synthesizeFloatingPointEqualitySystem(
		&compactAssignments, &compactAssignmentCount,
		[]FloatingPointEqualityRelation{equal12, distinct23, nanSelf},
	); unsatisfiable || !synthesized {
		t.Fatalf(
			"compact graph synthesis=(unsat=%v, synthesized=%v)",
			unsatisfiable, synthesized,
		)
	}
	solver := AssertFloatingPointEqualityRelation(1, New(), equal12)
	solver = AssertFloatingPointEqualityRelation(2, solver, distinct23)
	solver = AssertFloatingPointEqualityRelation(3, solver, nanSelf)
	result, ok := Check(solver).(Satisfiable)
	if !ok {
		t.Fatal("expected satisfiable shared binary128 equality graph")
	}
	values := make([]FloatingPointValue, 4)
	for index := range values {
		bits, found := FloatingPointSymbolModelBits(result.Value, index+1)
		if !found || bits.Width() != 128 {
			t.Fatalf("symbol %d missing from shared model", index+1)
		}
		values[index] = FloatingPointFromBits(15, 113, bits)
	}
	if !FloatingPointEqual(values[0], values[1]) ||
		FloatingPointEqual(values[1], values[2]) ||
		FloatingPointEqual(values[3], values[3]) {
		t.Fatal("shared equality model violates IEEE equality semantics")
	}
}

func TestSharedFloatingPointEqualityContradictions(t *testing.T) {
	positive12 := NewFloatingPointEqualityRelation(8, 24, 1, 2)
	positive23 := NewFloatingPointEqualityRelation(8, 24, 2, 3)
	negative13 := NewFloatingPointEqualityRelation(8, 24, 1, 3)
	negative13.Negated = true
	positiveSelf := NewFloatingPointEqualityRelation(8, 24, 1, 1)
	negativeSelf := positiveSelf
	negativeSelf.Negated = true
	for _, test := range []struct {
		name      string
		relations []FloatingPointEqualityRelation
	}{
		{"positive-chain-disequality", []FloatingPointEqualityRelation{
			positive12, positive23, negative13,
		}},
		{"positive-and-negated-self", []FloatingPointEqualityRelation{
			positiveSelf, negativeSelf,
		}},
		{"negated-self-before-positive", []FloatingPointEqualityRelation{
			negativeSelf, positiveSelf,
		}},
	} {
		t.Run(test.name, func(t *testing.T) {
			solver := New()
			for index, relation := range test.relations {
				solver = AssertFloatingPointEqualityRelation(
					index+1, solver, relation,
				)
			}
			if _, ok := Check(solver).(Unsatisfiable); !ok {
				t.Fatal("expected shared equality contradiction")
			}
		})
	}
}

func BenchmarkSharedFloatingPointEqualityGraph(b *testing.B) {
	equal12 := NewFloatingPointEqualityRelation(8, 24, 1, 2)
	distinct23 := NewFloatingPointEqualityRelation(8, 24, 2, 3)
	distinct23.Negated = true
	for b.Loop() {
		solver := AssertFloatingPointEqualityRelation(1, New(), equal12)
		solver = AssertFloatingPointEqualityRelation(2, solver, distinct23)
		result, ok := Check(solver).(Satisfiable)
		if !ok {
			b.Fatal("unexpected result")
		}
		if _, found := FloatingPointSymbolModelBits(result.Value, 3); !found {
			b.Fatal("incomplete model")
		}
	}
}

func TestCompactFloatingPointMinMaxWithAssignedSymbols(t *testing.T) {
	solver := New()
	solver = Assert(1, solver, BitVectorRelation{
		Width: 32, SymbolID: 1, Value: NewBitVectorUint64(32, 0xbf800000),
	})
	solver = Assert(2, solver, BitVectorRelation{
		Width: 32, SymbolID: 2, Value: NewBitVectorUint64(32, 0x3f800000),
	})
	solver = AssertFloatingPointMinMaxRelation(
		3, solver,
		NewFloatingPointMinMaxRelation(
			8, 24, 1, 2, FloatingPointOperationMin,
			NewBitVectorUint64(32, 0xbf800000),
		),
	)
	if _, ok := Check(solver).(Satisfiable); !ok {
		t.Fatalf("expected satisfiable compact fp.min, got %#v", Check(solver))
	}
}

func TestUnconstrainedFloatingPointMinMaxCanonicalModels(t *testing.T) {
	targets := []FloatingPointValue{
		FloatingPointPositiveZero(15, 113),
		FloatingPointNegativeZero(15, 113),
		FloatingPointPositiveInfinity(15, 113),
		FloatingPointNegativeInfinity(15, 113),
		FloatingPointNaN(15, 113),
		FloatingPointFromRational(
			15, 113, RoundNearestTiesToEven(), NewRational(-3, 2),
		),
	}
	for _, operation := range []uint8{
		FloatingPointOperationMin, FloatingPointOperationMax,
	} {
		for targetIndex, target := range targets {
			for _, negated := range []bool{false, true} {
				for _, same := range []bool{false, true} {
					rightID := 2
					if same {
						rightID = 1
					}
					relation := NewFloatingPointMinMaxRelation(
						15, 113, 1, rightID, operation,
						FloatingPointBits(target),
					)
					relation.Negated = negated
					result, ok := Check(AssertFloatingPointMinMaxRelation(
						1, New(), relation,
					)).(Satisfiable)
					if !ok {
						t.Fatalf(
							"operation=%d target=%d negated=%v same=%v was not satisfiable",
							operation, targetIndex, negated, same,
						)
					}
					leftBits, leftFound := FloatingPointSymbolModelBits(
						result.Value, 1,
					)
					rightBits, rightFound := FloatingPointSymbolModelBits(
						result.Value, rightID,
					)
					if !leftFound || !rightFound ||
						leftBits.Width() != 128 || rightBits.Width() != 128 {
						t.Fatal("canonical min/max model is incomplete")
					}
					left := FloatingPointFromBits(15, 113, leftBits)
					right := FloatingPointFromBits(15, 113, rightBits)
					selected := FloatingPointMin(left, right)
					if operation == FloatingPointOperationMax {
						selected = FloatingPointMax(left, right)
					}
					holds := EqualBitVectorValue(
						FloatingPointBits(selected), relation.Value,
					)
					if holds == negated {
						t.Fatal("canonical operands do not satisfy relation")
					}
				}
			}
		}
	}
}

func TestPairedUnconstrainedFloatingPointMinMaxCanonicalModels(t *testing.T) {
	minimum := NewFloatingPointMinMaxRelation(
		8, 24, 1, 2, FloatingPointOperationMin,
		NewBitVectorUint64(32, 0xc0400000),
	)
	maximum := NewFloatingPointMinMaxRelation(
		8, 24, 3, 4, FloatingPointOperationMax,
		NewBitVectorUint64(32, 0x3fc00000),
	)
	maximum.Negated = true
	solver := AssertFloatingPointMinMaxRelation(1, New(), minimum)
	solver = AssertFloatingPointMinMaxRelation(2, solver, maximum)
	result, ok := Check(solver).(Satisfiable)
	if !ok {
		t.Fatal("paired independent min/max images must be satisfiable")
	}
	for id := 1; id <= 4; id++ {
		if _, found := FloatingPointSymbolModelBits(result.Value, id); !found {
			t.Fatalf("symbol %d missing from paired model", id)
		}
	}
}

func TestCompactFloatingPointRoundToIntegralWithAssignedSymbol(t *testing.T) {
	solver := New()
	solver = Assert(1, solver, BitVectorRelation{
		Width: 32, SymbolID: 1, Value: NewBitVectorUint64(32, 0x3fc00000),
	})
	solver = AssertFloatingPointRoundToIntegralRelation(
		2, solver,
		NewFloatingPointRoundToIntegralRelation(
			8, 24, 1, RoundNearestTiesToEven(),
			NewBitVectorUint64(32, 0x40000000),
		),
	)
	if _, ok := Check(solver).(Satisfiable); !ok {
		t.Fatalf("expected satisfiable compact fp.roundToIntegral, got %#v", Check(solver))
	}
}

func TestCompactFloatingPointRoundToIntegralSynthesizesUnconstrainedSymbol(t *testing.T) {
	relation := NewFloatingPointRoundToIntegralRelation(
		8, 24, 1, RoundNearestTiesToEven(),
		NewBitVectorUint64(32, 0x40000000),
	)
	result, ok := Check(AssertFloatingPointRoundToIntegralRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatalf("expected synthesized fp.roundToIntegral model, got %#v", Check(
			AssertFloatingPointRoundToIntegralRelation(1, New(), relation),
		))
	}
	bits, found := FloatingPointSymbolModelBits(result.Value, 1)
	value, inline := bits.Uint64()
	if !found || !inline || value != 0x40000000 {
		t.Fatalf("unexpected synthesized source: %#x/%v/%v", value, found, inline)
	}

	relation.Value = NewBitVectorUint64(32, 0x3fc00000)
	if _, ok := Check(AssertFloatingPointRoundToIntegralRelation(
		1, New(), relation,
	)).(Unsatisfiable); !ok {
		t.Fatal("non-integral value cannot be an fp.roundToIntegral result")
	}
}

func TestFloatingPointRoundToIntegralDerivedModel(t *testing.T) {
	solver := New()
	solver = Assert(1, solver, BitVectorRelation{
		Width: 32, SymbolID: 1, Value: NewBitVectorUint64(32, 0xbfc00000),
	})
	result, ok := Check(solver).(Satisfiable)
	if !ok {
		t.Fatal("expected assigned floating-point source to be satisfiable")
	}
	rounded := FloatingPointRoundToIntegralBitVector(
		8, 24, 1, "value", RoundTowardZero(),
	)
	bits, found := BitVecModelValue(result.Value, rounded)
	value, inline := bits.Uint64()
	if !found || !inline || value != 0xbf800000 {
		t.Fatalf("unexpected derived fp.roundToIntegral model: %#x/%v/%v", value, found, inline)
	}
}

func TestSymbolicFloatingPointAddRelation(t *testing.T) {
	leftBits := NewBitVectorUint64(32, 0x3fc00000)
	rightBits := NewBitVectorUint64(32, 0x40100000)
	wantBits := NewBitVectorUint64(32, 0x40700000)
	solver := Assert(1, New(), BitVectorRelation{
		Width: 32, SymbolID: 1, Value: leftBits,
	})
	solver = Assert(2, solver, BitVectorRelation{
		Width: 32, SymbolID: 2, Value: rightBits,
	})
	solver = AssertFloatingPointAddRelation(
		3, solver,
		NewFloatingPointAddRelation(
			8, 24, 1, 2, RoundNearestTiesToEven(), wantBits,
		),
	)
	result, ok := Check(solver).(Satisfiable)
	if !ok {
		t.Fatalf("expected satisfiable fp.add, got %#v", Check(solver))
	}
	for id, want := range map[int]BitVectorValue{1: leftBits, 2: rightBits} {
		got, found := FloatingPointSymbolModelBits(result.Value, id)
		if !found || !EqualBitVectorValue(got, want) {
			t.Fatalf("symbol %d bits=%v,%v, want %v,true", id, got, found, want)
		}
	}
}

func TestSymbolicFloatingPointAddSynthesizesUnconstrainedOperands(t *testing.T) {
	tests := []struct {
		name          string
		target, right uint64
	}{
		{"finite", 0x40700000, 0x00000000},
		{"negative-zero", 0x80000000, 0x80000000},
		{"positive-infinity", 0x7f800000, 0x00000000},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointAddRelation(
				8, 24, 1, 2, RoundNearestTiesToEven(),
				NewBitVectorUint64(32, test.target),
			)
			result, ok := Check(AssertFloatingPointAddRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatalf("expected synthesized fp.add model, got %#v", Check(
					AssertFloatingPointAddRelation(1, New(), relation),
				))
			}
			left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
			right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
			leftValue, leftInline := left.Uint64()
			rightValue, rightInline := right.Uint64()
			if !leftFound || !rightFound || !leftInline || !rightInline ||
				leftValue != test.target || rightValue != test.right {
				t.Fatalf(
					"unexpected operands: left=%#x/%v right=%#x/%v",
					leftValue, leftFound, rightValue, rightFound,
				)
			}
		})
	}
}

func TestSymbolicFloatingPointAddSynthesizesBinary128Operands(t *testing.T) {
	target := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(3, 2),
	))
	relation := NewFloatingPointAddRelation(
		15, 113, 1, 2, RoundNearestTiesToEven(), target,
	)
	result, ok := Check(AssertFloatingPointAddRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized binary128 fp.add model")
	}
	left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
	right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
	if !leftFound || !rightFound ||
		!EqualBitVectorValue(left, target) ||
		!EqualBitVectorValue(right, NewBitVectorUint64(128, 0)) {
		t.Fatalf("unexpected binary128 operands: left=%v right=%v", left, right)
	}
}

func TestSymbolicFloatingPointSubRelation(t *testing.T) {
	leftBits := NewBitVectorUint64(32, 0x40700000)
	rightBits := NewBitVectorUint64(32, 0x40100000)
	wantBits := NewBitVectorUint64(32, 0x3fc00000)
	solver := Assert(1, New(), BitVectorRelation{
		Width: 32, SymbolID: 1, Value: leftBits,
	})
	solver = Assert(2, solver, BitVectorRelation{
		Width: 32, SymbolID: 2, Value: rightBits,
	})
	solver = AssertFloatingPointSubRelation(
		3, solver,
		NewFloatingPointSubRelation(
			8, 24, 1, 2, RoundNearestTiesToEven(), wantBits,
		),
	)
	if _, ok := Check(solver).(Satisfiable); !ok {
		t.Fatalf("expected satisfiable fp.sub, got %#v", Check(solver))
	}
}

func TestSymbolicFloatingPointSubSynthesizesUnconstrainedOperands(t *testing.T) {
	tests := []struct {
		name          string
		target, right uint64
	}{
		{"finite", 0x3fc00000, 0x00000000},
		{"negative-zero", 0x80000000, 0x00000000},
		{"negative-infinity", 0xff800000, 0x00000000},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointSubRelation(
				8, 24, 1, 2, RoundNearestTiesToEven(),
				NewBitVectorUint64(32, test.target),
			)
			result, ok := Check(AssertFloatingPointSubRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatalf("expected synthesized fp.sub model, got %#v", Check(
					AssertFloatingPointSubRelation(1, New(), relation),
				))
			}
			left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
			right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
			leftValue, leftInline := left.Uint64()
			rightValue, rightInline := right.Uint64()
			if !leftFound || !rightFound || !leftInline || !rightInline ||
				leftValue != test.target || rightValue != test.right {
				t.Fatalf(
					"unexpected operands: left=%#x/%v right=%#x/%v",
					leftValue, leftFound, rightValue, rightFound,
				)
			}
		})
	}
}

func TestSymbolicFloatingPointSubSynthesizesBinary128Operands(t *testing.T) {
	target := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(-3, 2),
	))
	relation := NewFloatingPointSubRelation(
		15, 113, 1, 2, RoundNearestTiesToEven(), target,
	)
	result, ok := Check(AssertFloatingPointSubRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized binary128 fp.sub model")
	}
	left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
	right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
	if !leftFound || !rightFound ||
		!EqualBitVectorValue(left, target) ||
		!EqualBitVectorValue(right, NewBitVectorUint64(128, 0)) {
		t.Fatalf("unexpected binary128 operands: left=%v right=%v", left, right)
	}
}

func TestSymbolicFloatingPointMulRelation(t *testing.T) {
	leftBits := NewBitVectorUint64(32, 0x3fc00000)
	rightBits := NewBitVectorUint64(32, 0x40100000)
	wantBits := NewBitVectorUint64(32, 0x40580000)
	solver := Assert(1, New(), BitVectorRelation{
		Width: 32, SymbolID: 1, Value: leftBits,
	})
	solver = Assert(2, solver, BitVectorRelation{
		Width: 32, SymbolID: 2, Value: rightBits,
	})
	solver = AssertFloatingPointMulRelation(
		3, solver,
		NewFloatingPointMulRelation(
			8, 24, 1, 2, RoundNearestTiesToEven(), wantBits,
		),
	)
	if _, ok := Check(solver).(Satisfiable); !ok {
		t.Fatalf("expected satisfiable fp.mul, got %#v", Check(solver))
	}
}

func TestSymbolicFloatingPointMulSynthesizesUnconstrainedOperands(t *testing.T) {
	for _, test := range []struct {
		name   string
		target uint64
	}{
		{"finite", 0x40580000},
		{"negative-zero", 0x80000000},
		{"positive-infinity", 0x7f800000},
	} {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointMulRelation(
				8, 24, 1, 2, RoundNearestTiesToEven(),
				NewBitVectorUint64(32, test.target),
			)
			result, ok := Check(AssertFloatingPointMulRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatalf("expected synthesized fp.mul model, got %#v", Check(
					AssertFloatingPointMulRelation(1, New(), relation),
				))
			}
			left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
			right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
			leftValue, leftInline := left.Uint64()
			rightValue, rightInline := right.Uint64()
			if !leftFound || !rightFound || !leftInline || !rightInline ||
				leftValue != test.target || rightValue != 0x3f800000 {
				t.Fatalf(
					"unexpected operands: left=%#x/%v right=%#x/%v",
					leftValue, leftFound, rightValue, rightFound,
				)
			}
		})
	}
}

func TestSymbolicFloatingPointMulSynthesizesBinary128Operands(t *testing.T) {
	target := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(27, 8),
	))
	one := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(1, 1),
	))
	relation := NewFloatingPointMulRelation(
		15, 113, 1, 2, RoundNearestTiesToEven(), target,
	)
	result, ok := Check(AssertFloatingPointMulRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized binary128 fp.mul model")
	}
	left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
	right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
	if !leftFound || !rightFound ||
		!EqualBitVectorValue(left, target) ||
		!EqualBitVectorValue(right, one) {
		t.Fatalf("unexpected binary128 operands: left=%v right=%v", left, right)
	}
}

func TestSymbolicFloatingPointDivRelation(t *testing.T) {
	leftBits := NewBitVectorUint64(32, 0x40400000)
	rightBits := NewBitVectorUint64(32, 0x40000000)
	wantBits := NewBitVectorUint64(32, 0x3fc00000)
	solver := Assert(1, New(), BitVectorRelation{
		Width: 32, SymbolID: 1, Value: leftBits,
	})
	solver = Assert(2, solver, BitVectorRelation{
		Width: 32, SymbolID: 2, Value: rightBits,
	})
	solver = AssertFloatingPointDivRelation(
		3, solver,
		NewFloatingPointDivRelation(
			8, 24, 1, 2, RoundNearestTiesToEven(), wantBits,
		),
	)
	if _, ok := Check(solver).(Satisfiable); !ok {
		t.Fatalf("expected satisfiable fp.div, got %#v", Check(solver))
	}
}

func TestSymbolicFloatingPointDivSynthesizesUnconstrainedOperands(t *testing.T) {
	for _, test := range []struct {
		name   string
		target uint64
	}{
		{"finite", 0x3eaaaaab},
		{"negative-zero", 0x80000000},
		{"negative-infinity", 0xff800000},
	} {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointDivRelation(
				8, 24, 1, 2, RoundNearestTiesToEven(),
				NewBitVectorUint64(32, test.target),
			)
			result, ok := Check(AssertFloatingPointDivRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatalf("expected synthesized fp.div model, got %#v", Check(
					AssertFloatingPointDivRelation(1, New(), relation),
				))
			}
			left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
			right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
			leftValue, leftInline := left.Uint64()
			rightValue, rightInline := right.Uint64()
			if !leftFound || !rightFound || !leftInline || !rightInline ||
				leftValue != test.target || rightValue != 0x3f800000 {
				t.Fatalf(
					"unexpected operands: left=%#x/%v right=%#x/%v",
					leftValue, leftFound, rightValue, rightFound,
				)
			}
		})
	}
}

func TestSymbolicFloatingPointDivSynthesizesBinary128Operands(t *testing.T) {
	target := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(1, 3),
	))
	one := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(1, 1),
	))
	relation := NewFloatingPointDivRelation(
		15, 113, 1, 2, RoundNearestTiesToEven(), target,
	)
	result, ok := Check(AssertFloatingPointDivRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized binary128 fp.div model")
	}
	left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
	right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
	if !leftFound || !rightFound ||
		!EqualBitVectorValue(left, target) ||
		!EqualBitVectorValue(right, one) {
		t.Fatalf("unexpected binary128 operands: left=%v right=%v", left, right)
	}
}

func TestSymbolicFloatingPointFMARelation(t *testing.T) {
	leftBits := NewBitVectorUint64(32, 0x3f800001)
	rightBits := NewBitVectorUint64(32, 0x3f7fffff)
	addendBits := NewBitVectorUint64(32, 0xbf800000)
	wantBits := NewBitVectorUint64(32, 0x337ffffe)
	solver := Assert(1, New(), BitVectorRelation{
		Width: 32, SymbolID: 1, Value: leftBits,
	})
	solver = Assert(2, solver, BitVectorRelation{
		Width: 32, SymbolID: 2, Value: rightBits,
	})
	solver = Assert(3, solver, BitVectorRelation{
		Width: 32, SymbolID: 3, Value: addendBits,
	})
	solver = AssertFloatingPointFMARelation(
		4, solver,
		NewFloatingPointFMARelation(
			8, 24, 1, 2, 3, RoundNearestTiesToEven(), wantBits,
		),
	)
	if _, ok := Check(solver).(Satisfiable); !ok {
		t.Fatalf("expected satisfiable fp.fma, got %#v", Check(solver))
	}
}

func TestSymbolicFloatingPointFMASynthesizesUnconstrainedOperands(t *testing.T) {
	for _, test := range []struct {
		name           string
		target, addend uint64
	}{
		{"finite", 0x337ffffe, 0x00000000},
		{"negative-zero", 0x80000000, 0x80000000},
		{"positive-infinity", 0x7f800000, 0x00000000},
	} {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointFMARelation(
				8, 24, 1, 2, 3, RoundNearestTiesToEven(),
				NewBitVectorUint64(32, test.target),
			)
			result, ok := Check(AssertFloatingPointFMARelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatalf("expected synthesized fp.fma model, got %#v", Check(
					AssertFloatingPointFMARelation(1, New(), relation),
				))
			}
			left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
			right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
			addend, addendFound := FloatingPointSymbolModelBits(result.Value, 3)
			leftValue, leftInline := left.Uint64()
			rightValue, rightInline := right.Uint64()
			addendValue, addendInline := addend.Uint64()
			if !leftFound || !rightFound || !addendFound ||
				!leftInline || !rightInline || !addendInline ||
				leftValue != test.target || rightValue != 0x3f800000 ||
				addendValue != test.addend {
				t.Fatalf(
					"unexpected operands: left=%#x right=%#x addend=%#x",
					leftValue, rightValue, addendValue,
				)
			}
		})
	}
}

func TestSymbolicFloatingPointFMASynthesizesBinary128Operands(t *testing.T) {
	target := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(3, 2),
	))
	one := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(1, 1),
	))
	relation := NewFloatingPointFMARelation(
		15, 113, 1, 2, 3, RoundNearestTiesToEven(), target,
	)
	result, ok := Check(AssertFloatingPointFMARelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized binary128 fp.fma model")
	}
	left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
	right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
	addend, addendFound := FloatingPointSymbolModelBits(result.Value, 3)
	if !leftFound || !rightFound || !addendFound ||
		!EqualBitVectorValue(left, target) ||
		!EqualBitVectorValue(right, one) ||
		!EqualBitVectorValue(addend, NewBitVectorUint64(128, 0)) {
		t.Fatalf(
			"unexpected binary128 operands: left=%v right=%v addend=%v",
			left, right, addend,
		)
	}
}

func TestRepeatedOperandFloatingPointFMAImages(t *testing.T) {
	threeHalves := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(3, 2),
	))
	threeQuarters := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(3, 4),
	))
	for _, test := range []struct {
		name                  string
		left, right, addendID int
		target                BitVectorValue
	}{
		{"repeated-multiplicand", 1, 1, 2, threeHalves},
		{"left-is-addend", 1, 2, 1, threeHalves},
		{"right-is-addend", 2, 1, 1, threeHalves},
		{"all-three", 1, 1, 1, threeQuarters},
	} {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointFMARelation(
				15, 113, test.left, test.right, test.addendID,
				RoundNearestTiesToEven(), test.target,
			)
			result, ok := Check(AssertFloatingPointFMARelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatal("expected repeated-operand binary128 fp.fma model")
			}
			leftBits, leftFound := FloatingPointSymbolModelBits(
				result.Value, test.left,
			)
			rightBits, rightFound := FloatingPointSymbolModelBits(
				result.Value, test.right,
			)
			addendBits, addendFound := FloatingPointSymbolModelBits(
				result.Value, test.addendID,
			)
			if !leftFound || !rightFound || !addendFound {
				t.Fatal("repeated-operand fp.fma model is incomplete")
			}
			actual := FloatingPointFMA(
				RoundNearestTiesToEven(),
				FloatingPointFromBits(15, 113, leftBits),
				FloatingPointFromBits(15, 113, rightBits),
				FloatingPointFromBits(15, 113, addendBits),
			)
			if !EqualBitVectorValue(FloatingPointBits(actual), test.target) {
				t.Fatal("repeated-operand fp.fma model misses target")
			}
		})
	}
}

func TestSymbolicFloatingPointSqrtRelation(t *testing.T) {
	valueBits := NewBitVectorUint64(32, 0x40000000)
	wantBits := NewBitVectorUint64(32, 0x3fb504f3)
	solver := Assert(1, New(), BitVectorRelation{
		Width: 32, SymbolID: 1, Value: valueBits,
	})
	solver = AssertFloatingPointSqrtRelation(
		2, solver,
		NewFloatingPointSqrtRelation(
			8, 24, 1, RoundNearestTiesToEven(), wantBits,
		),
	)
	if _, ok := Check(solver).(Satisfiable); !ok {
		t.Fatalf("expected satisfiable fp.sqrt, got %#v", Check(solver))
	}
}

func TestSymbolicFloatingPointSqrtSynthesizesUnconstrainedSource(t *testing.T) {
	for _, test := range []struct {
		name   string
		target uint64
	}{
		{"finite", 0x3fb504f3},
		{"negative-zero", 0x80000000},
		{"positive-infinity", 0x7f800000},
	} {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointSqrtRelation(
				8, 24, 1, RoundNearestTiesToEven(),
				NewBitVectorUint64(32, test.target),
			)
			result, ok := Check(AssertFloatingPointSqrtRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatalf("expected synthesized fp.sqrt model")
			}
			source, found := FloatingPointSymbolModelBits(result.Value, 1)
			if !found {
				t.Fatal("synthesized fp.sqrt source missing from model")
			}
			root := FloatingPointSqrt(
				RoundNearestTiesToEven(),
				FloatingPointFromBits(8, 24, source),
			)
			if actual, inline := FloatingPointBits(root).Uint64(); !inline || actual != test.target {
				t.Fatalf("sqrt(model source)=%#x, want %#x", actual, test.target)
			}
		})
	}
}

func TestSymbolicFloatingPointSqrtRejectsNegativeResult(t *testing.T) {
	relation := NewFloatingPointSqrtRelation(
		8, 24, 1, RoundNearestTiesToEven(),
		NewBitVectorUint64(32, 0xbf800000),
	)
	if _, ok := Check(AssertFloatingPointSqrtRelation(
		1, New(), relation,
	)).(Unsatisfiable); !ok {
		t.Fatal("expected negative nonzero fp.sqrt result to be unsatisfiable")
	}
}

func TestSymbolicFloatingPointSqrtSynthesizesBinary128Source(t *testing.T) {
	target := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(2, 1),
	))
	relation := NewFloatingPointSqrtRelation(
		15, 113, 1, RoundNearestTiesToEven(), target,
	)
	result, ok := Check(AssertFloatingPointSqrtRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized binary128 fp.sqrt model")
	}
	source, found := FloatingPointSymbolModelBits(result.Value, 1)
	if !found {
		t.Fatal("synthesized binary128 fp.sqrt source missing from model")
	}
	root := FloatingPointSqrt(
		RoundNearestTiesToEven(),
		FloatingPointFromBits(15, 113, source),
	)
	if !EqualBitVectorValue(FloatingPointBits(root), target) {
		t.Fatalf("sqrt(model source)=%v, want %v", FloatingPointBits(root), target)
	}
}

func TestSymbolicFloatingPointRemRelation(t *testing.T) {
	leftBits := NewBitVectorUint64(32, 0x40400000)
	rightBits := NewBitVectorUint64(32, 0x40000000)
	wantBits := NewBitVectorUint64(32, 0xbf800000)
	solver := Assert(1, New(), BitVectorRelation{
		Width: 32, SymbolID: 1, Value: leftBits,
	})
	solver = Assert(2, solver, BitVectorRelation{
		Width: 32, SymbolID: 2, Value: rightBits,
	})
	solver = AssertFloatingPointRemRelation(
		3, solver,
		NewFloatingPointRemRelation(8, 24, 1, 2, wantBits),
	)
	if _, ok := Check(solver).(Satisfiable); !ok {
		t.Fatalf("expected satisfiable fp.rem, got %#v", Check(solver))
	}
}

func TestSymbolicFloatingPointRemSynthesizesUnconstrainedOperands(t *testing.T) {
	for _, test := range []struct {
		name   string
		target uint64
	}{
		{"finite", 0xbf800000},
		{"negative-zero", 0x80000000},
		{"subnormal", 0x00000001},
		{"canonical-nan", 0x7fc00000},
	} {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointRemRelation(
				8, 24, 1, 2, NewBitVectorUint64(32, test.target),
			)
			result, ok := Check(AssertFloatingPointRemRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatal("expected synthesized fp.rem model")
			}
			left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
			right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
			leftValue, leftInline := left.Uint64()
			rightValue, rightInline := right.Uint64()
			if !leftFound || !rightFound || !leftInline || !rightInline ||
				leftValue != test.target || rightValue != 0x7f800000 {
				t.Fatalf(
					"unexpected operands: left=%#x right=%#x",
					leftValue, rightValue,
				)
			}
		})
	}
}

func TestRepeatedOperandFloatingPointImages(t *testing.T) {
	const exponentBits, significandBits = 15, 113
	modeValue := RoundTowardNegative()
	mode := floatingPointRoundingModeCode(modeValue)
	one := floatingPointFromRational(
		mode, exponentBits, significandBits, NewRational(1, 1),
	)
	negativeOne := floatingPointFromRational(
		mode, exponentBits, significandBits, NewRational(-1, 1),
	)
	for _, test := range []struct {
		name   string
		target FloatingPointValue
		assert func(BitVectorValue) CheckResult
		eval   func(FloatingPointValue) FloatingPointValue
	}{
		{
			"add",
			floatingPointAdd(mode, one, one),
			func(target BitVectorValue) CheckResult {
				return Check(AssertFloatingPointAddRelation(
					1, New(), NewFloatingPointAddRelation(
						exponentBits, significandBits, 1, 1, modeValue, target,
					),
				))
			},
			func(value FloatingPointValue) FloatingPointValue {
				return floatingPointAdd(mode, value, value)
			},
		},
		{
			"subtract",
			floatingPointSub(mode, one, one),
			func(target BitVectorValue) CheckResult {
				return Check(AssertFloatingPointSubRelation(
					1, New(), NewFloatingPointSubRelation(
						exponentBits, significandBits, 1, 1, modeValue, target,
					),
				))
			},
			func(value FloatingPointValue) FloatingPointValue {
				return floatingPointSub(mode, value, value)
			},
		},
		{
			"multiply",
			floatingPointMul(mode, negativeOne, negativeOne),
			func(target BitVectorValue) CheckResult {
				return Check(AssertFloatingPointMulRelation(
					1, New(), NewFloatingPointMulRelation(
						exponentBits, significandBits, 1, 1, modeValue, target,
					),
				))
			},
			func(value FloatingPointValue) FloatingPointValue {
				return floatingPointMul(mode, value, value)
			},
		},
		{
			"divide",
			floatingPointDiv(mode, one, one),
			func(target BitVectorValue) CheckResult {
				return Check(AssertFloatingPointDivRelation(
					1, New(), NewFloatingPointDivRelation(
						exponentBits, significandBits, 1, 1, modeValue, target,
					),
				))
			},
			func(value FloatingPointValue) FloatingPointValue {
				return floatingPointDiv(mode, value, value)
			},
		},
		{
			"remainder-negative",
			floatingPointRem(negativeOne, negativeOne),
			func(target BitVectorValue) CheckResult {
				return Check(AssertFloatingPointRemRelation(
					1, New(), NewFloatingPointRemRelation(
						exponentBits, significandBits, 1, 1, target,
					),
				))
			},
			func(value FloatingPointValue) FloatingPointValue {
				return floatingPointRem(value, value)
			},
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			target := FloatingPointBits(test.target)
			result, ok := test.assert(target).(Satisfiable)
			if !ok {
				t.Fatal("expected repeated-operand image model")
			}
			bits, found := FloatingPointSymbolModelBits(result.Value, 1)
			if !found || bits.Width() != 128 {
				t.Fatal("repeated-operand model is incomplete")
			}
			actual := test.eval(FloatingPointFromBits(
				exponentBits, significandBits, bits,
			))
			if !EqualBitVectorValue(FloatingPointBits(actual), target) {
				t.Fatal("repeated-operand model does not reproduce target")
			}
		})
	}
}

func TestRepeatedOperandFloatingPointRejectsOutsideImages(t *testing.T) {
	one := FloatingPointBits(floatingPointFromRational(
		1, 8, 24, NewRational(1, 1),
	))
	zero := FloatingPointBits(FloatingPointPositiveZero(8, 24))
	if _, ok := Check(AssertFloatingPointSubRelation(
		1, New(), NewFloatingPointSubRelation(
			8, 24, 1, 1, RoundNearestTiesToEven(), one,
		),
	)).(Unsatisfiable); !ok {
		t.Fatal("x-x cannot equal one")
	}
	if _, ok := Check(AssertFloatingPointDivRelation(
		1, New(), NewFloatingPointDivRelation(
			8, 24, 1, 1, RoundNearestTiesToEven(), zero,
		),
	)).(Unsatisfiable); !ok {
		t.Fatal("x/x cannot equal zero")
	}
	negativeOne := FloatingPointBits(floatingPointFromRational(
		1, 8, 24, NewRational(-1, 1),
	))
	if _, ok := Check(AssertFloatingPointMulRelation(
		1, New(), NewFloatingPointMulRelation(
			8, 24, 1, 1, RoundNearestTiesToEven(), negativeOne,
		),
	)).(Unsatisfiable); !ok {
		t.Fatal("x*x cannot equal a negative value")
	}
	if _, ok := Check(AssertFloatingPointRemRelation(
		1, New(), NewFloatingPointRemRelation(8, 24, 1, 1, one),
	)).(Unsatisfiable); !ok {
		t.Fatal("rem x x cannot equal one")
	}
}

func TestSymbolicFloatingPointRemRejectsInfiniteResult(t *testing.T) {
	for _, target := range []uint64{0x7f800000, 0xff800000} {
		relation := NewFloatingPointRemRelation(
			8, 24, 1, 2, NewBitVectorUint64(32, target),
		)
		if _, ok := Check(AssertFloatingPointRemRelation(
			1, New(), relation,
		)).(Unsatisfiable); !ok {
			t.Fatalf("expected fp.rem result %#x to be unsatisfiable", target)
		}
	}
}

func TestSymbolicFloatingPointRemSynthesizesBinary128Operands(t *testing.T) {
	target := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(-3, 2),
	))
	infinity := FloatingPointBits(FloatingPointPositiveInfinity(15, 113))
	relation := NewFloatingPointRemRelation(15, 113, 1, 2, target)
	result, ok := Check(AssertFloatingPointRemRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized binary128 fp.rem model")
	}
	left, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
	right, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
	if !leftFound || !rightFound ||
		!EqualBitVectorValue(left, target) ||
		!EqualBitVectorValue(right, infinity) {
		t.Fatalf("unexpected binary128 operands: left=%v right=%v", left, right)
	}
}

func TestFloatingPointMinMaxBitBlastFallback(t *testing.T) {
	expected := NewBitVectorUint64(32, 0xbf800000)
	relation := NewFloatingPointMinMaxRelation(
		8, 24, 1, 2, FloatingPointOperationMin, expected,
	)
	result, ok := Check(AssertFloatingPointMinMaxRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("unconstrained fp.min equality must be satisfiable")
	}
	leftBits, leftFound := FloatingPointSymbolModelBits(result.Value, 1)
	rightBits, rightFound := FloatingPointSymbolModelBits(result.Value, 2)
	if !leftFound || !rightFound {
		t.Fatal("bit-blasted fp.min must model both operands")
	}
	selected := FloatingPointMin(
		FloatingPointFromBits(8, 24, leftBits),
		FloatingPointFromBits(8, 24, rightBits),
	)
	if !EqualBitVectorValue(FloatingPointBits(selected), expected) {
		t.Fatalf("invalid fp.min model: left=%v right=%v", leftBits, rightBits)
	}
	selectedBits, selectedFound := BitVecModelValue(
		result.Value,
		FloatingPointMinMaxBitVector(
			8, 24, 1, 2, "left", "right", FloatingPointOperationMin,
		),
	)
	if !selectedFound || !EqualBitVectorValue(selectedBits, expected) {
		t.Fatalf("derived fp.min model=%v/%v", selectedBits, selectedFound)
	}
}
