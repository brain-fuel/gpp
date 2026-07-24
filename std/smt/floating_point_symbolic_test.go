package smt

import "testing"

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
