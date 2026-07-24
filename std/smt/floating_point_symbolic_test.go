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
