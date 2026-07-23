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
