package smt

import "testing"

func TestGroundIntegerSequenceEvaluation(t *testing.T) {
	wide, err := ParseIntegerValue("123456789012345678901234567890")
	if err != nil {
		t.Fatal(err)
	}
	empty := SequenceEmpty[IntSort]()
	first := SequenceUnit[IntSort](Integer{Value: 7})
	second := SequenceUnit[IntSort](IntegerTerm(wide))
	sequence := SequenceConcat(first, empty, second)
	same := SequenceConcat(
		SequenceUnit[IntSort](Integer{Value: 7}),
		SequenceUnit[IntSort](IntegerTerm(wide)),
	)
	different := SequenceConcat(
		SequenceUnit[IntSort](Integer{Value: 7}),
		SequenceUnit[IntSort](Integer{Value: 8}),
	)
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: sequence, Right: same},
		Not{Value: Equal{Left: sequence, Right: different}},
		Equal{Left: SequenceLength(sequence), Right: Integer{Value: 2}},
		Less{Left: SequenceLength(empty), Right: SequenceLength(sequence)},
		LessEqual{
			Left: Add{Values: []Term[IntSort]{
				SequenceLength(first),
				SequenceLength(second),
			}},
			Right: SequenceLength(sequence),
		},
		Or{Values: []Term[BoolSort]{
			Equal{Left: sequence, Right: different},
			Equal{Left: sequence, Right: same},
		}},
	}}
	checked := Check(Assert(1, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	if length, found := IntValue(result.Value, SequenceLength(sequence)); !found || length != 2 {
		t.Fatalf("length=(%d,%v)", length, found)
	}
	value, found := IntegerSequenceModelValue(result.Value, sequence)
	if !found || value.Len() != 2 {
		t.Fatalf("sequence len=(%d,%v)", value.Len(), found)
	}
	if element, ok := value.At(0); !ok || CompareIntegerValue(element, NewIntegerValue(7)) != 0 {
		t.Fatalf("first=(%v,%v)", element, ok)
	}
	if element, ok := value.At(1); !ok || CompareIntegerValue(element, wide) != 0 {
		t.Fatalf("second=(%v,%v)", element, ok)
	}
	if _, ok := value.At(2); ok {
		t.Fatal("out-of-range element reported present")
	}
}

func TestGroundIntegerSequenceContradiction(t *testing.T) {
	sequence := SequenceConcat(
		SequenceUnit[IntSort](Integer{Value: 1}),
		SequenceUnit[IntSort](Integer{Value: 2}),
	)
	formula := And{Values: []Term[BoolSort]{
		Equal{
			Left:  sequence,
			Right: SequenceUnit[IntSort](Integer{Value: 1}),
		},
		Equal{Left: SequenceLength(sequence), Right: Integer{Value: 2}},
	}}
	checked := Check(Assert(2, New(), formula))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("result=%T", checked)
	}
}

func TestGroundIntegerSequenceInlineOverflow(t *testing.T) {
	units := make([]Term[SequenceSort[IntSort]], 10)
	for index := range units {
		units[index] = SequenceUnit[IntSort](Integer{Value: int64(index)})
	}
	sequence := SequenceConcat(units...)
	formula := Equal{Left: SequenceLength(sequence), Right: Integer{Value: 10}}
	checked := Check(Assert(3, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	value, found := IntegerSequenceModelValue(result.Value, sequence)
	if !found || value.Len() != 10 {
		t.Fatalf("sequence len=(%d,%v)", value.Len(), found)
	}
	for index := 0; index < 10; index++ {
		element, ok := value.At(index)
		if !ok || CompareIntegerValue(element, NewIntegerValue(int64(index))) != 0 {
			t.Fatalf("element %d=(%v,%v)", index, element, ok)
		}
	}
}

func TestGroundIntegerSequenceIndexedOperations(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	sequence := SequenceConcat(unit(1), unit(2), unit(3), unit(2))
	pair := SequenceConcat(unit(2), unit(3))
	replaced := SequenceConcat(unit(1), unit(9), unit(2))
	inserted := SequenceConcat(unit(9), unit(1), unit(2), unit(3), unit(2))
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: SequenceAt(sequence, Integer{Value: 1}), Right: unit(2)},
		Equal{Left: SequenceAt(sequence, Integer{Value: -1}), Right: SequenceEmpty[IntSort]()},
		Equal{Left: SequenceAt(sequence, Integer{Value: 9}), Right: SequenceEmpty[IntSort]()},
		Equal{
			Left:  SequenceExtract(sequence, Integer{Value: 1}, Integer{Value: 2}),
			Right: pair,
		},
		Equal{
			Left:  SequenceExtract(sequence, Integer{Value: 3}, Integer{Value: 9}),
			Right: unit(2),
		},
		SequenceContains(sequence, pair),
		SequenceHasPrefix(sequence, SequenceConcat(unit(1), unit(2))),
		SequenceHasSuffix(sequence, SequenceConcat(unit(3), unit(2))),
		Equal{
			Left:  SequenceIndexOf(sequence, unit(2), Integer{Value: 2}),
			Right: Integer{Value: 3},
		},
		Equal{
			Left:  SequenceIndexOf(sequence, SequenceEmpty[IntSort](), Integer{Value: 4}),
			Right: Integer{Value: 4},
		},
		Equal{
			Left:  SequenceReplace(sequence, pair, unit(9)),
			Right: replaced,
		},
		Equal{
			Left:  SequenceReplace(sequence, SequenceEmpty[IntSort](), unit(9)),
			Right: inserted,
		},
	}}
	checked := Check(Assert(4, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	value, found := IntegerSequenceModelValue(
		result.Value,
		SequenceReplace(sequence, pair, unit(9)),
	)
	if !found || value.Len() != 3 {
		t.Fatalf("replacement len=(%d,%v)", value.Len(), found)
	}
}

func TestGroundAssignedSymbolicIntegerSequence(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	x := SequenceConst[IntSort](1, "x")
	ground := SequenceConcat(unit(1), unit(2), unit(3))
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: ground},
		SequenceContains(x, SequenceConcat(unit(2), unit(3))),
		Equal{Left: SequenceLength(x), Right: Integer{Value: 3}},
		Equal{Left: SequenceAt(x, Integer{Value: 1}), Right: unit(2)},
		Equal{
			Left:  SequenceReplace(x, unit(2), unit(9)),
			Right: SequenceConcat(unit(1), unit(9), unit(3)),
		},
	}}
	checked := Check(Assert(5, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	value, found := IntegerSequenceModelValue(result.Value, x)
	if !found || value.Len() != 3 {
		t.Fatalf("x len=(%d,%v)", value.Len(), found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	if length, found := IntValue(result.Value, SequenceLength(x)); !found || length != 3 {
		t.Fatalf("length=(%d,%v)", length, found)
	}

	conflicting := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: ground},
		Equal{Left: x, Right: SequenceConcat(unit(1), unit(2))},
	}}
	checked = Check(Assert(6, New(), conflicting))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("conflicting result=%T", checked)
	}

	unbound := SequenceContains(x, unit(2))
	symbolic, ok := Check(Assert(7, New(), unbound)).(Satisfiable)
	if !ok {
		t.Fatalf("unbound result=%T", Check(Assert(7, New(), unbound)))
	}
	if value, found := IntegerSequenceModelValue(symbolic.Value, x); !found || value.Len() != 1 {
		t.Fatalf("symbolic x len=(%d,%v)", value.Len(), found)
	}

	assumed := CheckAssuming(
		New(),
		Equal{Left: x, Right: ground},
		SequenceContains(x, unit(2)),
	)
	assumptionResult, ok := assumed.(AssumptionsSatisfiable)
	if !ok {
		t.Fatalf("assumption result=%T", assumed)
	}
	if value, found := IntegerSequenceModelValue(assumptionResult.Value, x); !found || value.Len() != 3 {
		t.Fatalf("assumption x len=(%d,%v)", value.Len(), found)
	}
}

func TestPositiveSymbolicIntegerSequenceWitness(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	x := SequenceConst[IntSort](10, "x")
	y := SequenceConst[IntSort](11, "y")
	formula := And{Values: []Term[BoolSort]{
		SequenceHasPrefix(x, SequenceConcat(unit(1), unit(2))),
		SequenceHasPrefix(x, unit(1)),
		SequenceContains(x, SequenceConcat(unit(3), unit(4))),
		SequenceContains(x, unit(3)),
		SequenceHasSuffix(x, SequenceConcat(unit(5), unit(6))),
		SequenceHasSuffix(x, unit(6)),
		SequenceContains(y, SequenceConcat(unit(9), unit(8))),
	}}
	checked := Check(Assert(8, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	if value, found := IntegerSequenceModelValue(result.Value, x); !found || value.Len() != 6 {
		t.Fatalf("x len=(%d,%v)", value.Len(), found)
	}
	if value, found := IntegerSequenceModelValue(result.Value, y); !found || value.Len() != 2 {
		t.Fatalf("y len=(%d,%v)", value.Len(), found)
	}

	incompatible := And{Values: []Term[BoolSort]{
		SequenceHasPrefix(x, unit(1)),
		SequenceHasPrefix(x, unit(2)),
	}}
	if checked := Check(Assert(9, New(), incompatible)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("incompatible result=%T", checked)
	}

	unsupported := Not{Value: SequenceContains(x, unit(1))}
	if checked := Check(Assert(10, New(), unsupported)); func() bool {
		_, ok := checked.(Unknown)
		return ok
	}() == false {
		t.Fatalf("unsupported result=%T", checked)
	}
}
