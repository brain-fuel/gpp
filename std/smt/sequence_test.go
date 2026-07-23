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

func TestExactLengthSymbolicIntegerSequenceWitness(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	x := SequenceConst[IntSort](20, "x")
	formula := And{Values: []Term[BoolSort]{
		SequenceHasPrefix(x, SequenceConcat(unit(1), unit(2))),
		SequenceContains(x, unit(3)),
		SequenceHasSuffix(x, SequenceConcat(unit(5), unit(6))),
		Equal{Left: SequenceLength(x), Right: Integer{Value: 6}},
	}}
	checked := Check(Assert(11, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	value, found := IntegerSequenceModelValue(result.Value, x)
	if !found || value.Len() != 6 {
		t.Fatalf("x len=(%d,%v)", value.Len(), found)
	}
	padding, ok := value.At(3)
	if !ok || CompareIntegerValue(padding, IntegerValue{}) != 0 {
		t.Fatalf("padding=(%v,%v)", padding, ok)
	}

	empty := SequenceConst[IntSort](21, "empty")
	emptyResult, ok := Check(Assert(
		12,
		New(),
		Equal{Left: SequenceLength(empty), Right: Integer{Value: 0}},
	)).(Satisfiable)
	if !ok {
		t.Fatal("zero length must construct the empty sequence")
	}
	if value, found := IntegerSequenceModelValue(emptyResult.Value, empty); !found || value.Len() != 0 {
		t.Fatalf("empty len=(%d,%v)", value.Len(), found)
	}

	conflicting := And{Values: []Term[BoolSort]{
		Equal{Left: SequenceLength(x), Right: Integer{Value: 2}},
		Equal{Left: SequenceLength(x), Right: Integer{Value: 3}},
	}}
	if checked := Check(Assert(13, New(), conflicting)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}

	tooShort := And{Values: []Term[BoolSort]{
		SequenceContains(x, SequenceConcat(unit(1), unit(2), unit(3))),
		Equal{Left: SequenceLength(x), Right: Integer{Value: 2}},
	}}
	if checked := Check(Assert(14, New(), tooShort)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("too-short result=%T", checked)
	}

	overlapRequired := And{Values: []Term[BoolSort]{
		SequenceHasPrefix(x, SequenceConcat(unit(1), unit(2))),
		SequenceHasSuffix(x, SequenceConcat(unit(2), unit(3))),
		Equal{Left: SequenceLength(x), Right: Integer{Value: 3}},
	}}
	overlapResult, ok := Check(Assert(15, New(), overlapRequired)).(Satisfiable)
	if !ok {
		t.Fatal("overlap must be satisfiable")
	}
	if value, found := IntegerSequenceModelValue(overlapResult.Value, x); !found || value.Len() != 3 {
		t.Fatalf("overlap len=(%d,%v)", value.Len(), found)
	}

	negative := Equal{Left: SequenceLength(x), Right: Integer{Value: -1}}
	if checked := Check(Assert(16, New(), negative)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("negative result=%T", checked)
	}
}

func TestRelationalLengthSymbolicIntegerSequenceWitness(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	x := SequenceConst[IntSort](30, "x")
	bounded := And{Values: []Term[BoolSort]{
		SequenceHasPrefix(x, unit(1)),
		SequenceHasSuffix(x, unit(3)),
		SequenceContains(x, unit(2)),
		LessEqual{Left: Integer{Value: 3}, Right: SequenceLength(x)},
		LessEqual{Left: SequenceLength(x), Right: Integer{Value: 5}},
	}}
	checked := Check(Assert(17, New(), bounded))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("bounded result=%T", checked)
	}
	value, found := IntegerSequenceModelValue(result.Value, x)
	if !found || value.Len() < 3 || value.Len() > 5 {
		t.Fatalf("bounded len=(%d,%v)", value.Len(), found)
	}
	if valid, found := BoolValue(result.Value, bounded); !found || !valid {
		t.Fatalf("bounded formula=(%v,%v)", valid, found)
	}

	strictMinimum := Less{
		Left:  Integer{Value: 5},
		Right: SequenceLength(x),
	}
	strictResult, ok := Check(Assert(18, New(), strictMinimum)).(Satisfiable)
	if !ok {
		t.Fatal("strict minimum must be satisfiable")
	}
	if value, found := IntegerSequenceModelValue(strictResult.Value, x); !found || value.Len() != 6 {
		t.Fatalf("strict minimum len=(%d,%v)", value.Len(), found)
	}

	conflicting := And{Values: []Term[BoolSort]{
		LessEqual{Left: Integer{Value: 4}, Right: SequenceLength(x)},
		LessEqual{Left: SequenceLength(x), Right: Integer{Value: 3}},
	}}
	if checked := Check(Assert(19, New(), conflicting)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}

	orderIndependent := And{Values: []Term[BoolSort]{
		LessEqual{Left: Integer{Value: 4}, Right: SequenceLength(x)},
		Equal{Left: SequenceLength(x), Right: Integer{Value: 3}},
	}}
	if checked := Check(Assert(20, New(), orderIndependent)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("order-independent result=%T", checked)
	}

	impossible := Less{
		Left:  SequenceLength(x),
		Right: Integer{Value: 0},
	}
	if checked := Check(Assert(21, New(), impossible)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestAffineLengthSymbolicIntegerSequenceWitness(t *testing.T) {
	x := SequenceConst[IntSort](40, "x")
	length := SequenceLength(x)
	twicePlusOne := Add{Values: []Term[IntSort]{
		IntegerScale{Coefficient: NewIntegerValue(2), Value: length},
		Integer{Value: 1},
	}}
	exact := Equal{Left: twicePlusOne, Right: Integer{Value: 7}}
	result, ok := Check(Assert(22, New(), exact)).(Satisfiable)
	if !ok {
		t.Fatal("affine equality must be satisfiable")
	}
	if value, found := IntegerSequenceModelValue(result.Value, x); !found || value.Len() != 3 {
		t.Fatalf("exact len=(%d,%v)", value.Len(), found)
	}

	nondivisible := Equal{
		Left:  IntegerScale{Coefficient: NewIntegerValue(2), Value: length},
		Right: Integer{Value: 3},
	}
	if checked := Check(Assert(23, New(), nondivisible)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("nondivisible result=%T", checked)
	}

	bounded := And{Values: []Term[BoolSort]{
		LessEqual{Left: twicePlusOne, Right: Integer{Value: 9}},
		Less{
			Left: Add{Values: []Term[IntSort]{
				IntegerScale{Coefficient: NewIntegerValue(-2), Value: length},
				Integer{Value: 1},
			}},
			Right: Integer{Value: -4},
		},
	}}
	boundedResult, ok := Check(Assert(24, New(), bounded)).(Satisfiable)
	if !ok {
		t.Fatal("affine bounds must be satisfiable")
	}
	if value, found := IntegerSequenceModelValue(boundedResult.Value, x); !found ||
		value.Len() < 3 || value.Len() > 4 {
		t.Fatalf("bounded len=(%d,%v)", value.Len(), found)
	}

	y := SequenceConst[IntSort](41, "y")
	multiple := Equal{
		Left:  Add{Values: []Term[IntSort]{SequenceLength(x), SequenceLength(y)}},
		Right: Integer{Value: 3},
	}
	multipleResult, ok := Check(Assert(25, New(), multiple)).(Satisfiable)
	if !ok {
		t.Fatal("two-symbol affine equality must be satisfiable")
	}
	xLength, xFound := IntValue(multipleResult.Value, SequenceLength(x))
	yLength, yFound := IntValue(multipleResult.Value, SequenceLength(y))
	if !xFound || !yFound || xLength+yLength != 3 {
		t.Fatalf("multiple-symbol lengths=(%d,%v)/(%d,%v)", xLength, xFound, yLength, yFound)
	}
}

func TestThreeSymbolAffineLengthIntegerSequenceWitness(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	x := SequenceConst[IntSort](43, "x")
	y := SequenceConst[IntSort](44, "y")
	z := SequenceConst[IntSort](45, "z")
	relation := Equal{
		Left: Add{Values: []Term[IntSort]{
			IntegerScale{
				Coefficient: NewIntegerValue(2),
				Value:       SequenceLength(x),
			},
			SequenceLength(y),
			SequenceLength(z),
		}},
		Right: Integer{Value: 7},
	}
	formula := And{Values: []Term[BoolSort]{
		relation,
		SequenceHasPrefix(x, SequenceConcat(unit(1), unit(2))),
		SequenceContains(y, unit(3)),
		SequenceHasSuffix(z, SequenceConcat(unit(4), unit(5))),
	}}
	checked := Check(Assert(26, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	xValue, xFound := IntegerSequenceModelValue(result.Value, x)
	yValue, yFound := IntegerSequenceModelValue(result.Value, y)
	zValue, zFound := IntegerSequenceModelValue(result.Value, z)
	if !xFound || !yFound || !zFound ||
		2*xValue.Len()+yValue.Len()+zValue.Len() != 7 {
		t.Fatalf(
			"lengths=(%d,%v)/(%d,%v)/(%d,%v)",
			xValue.Len(), xFound, yValue.Len(), yFound, zValue.Len(), zFound,
		)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	conflicting := And{Values: []Term[BoolSort]{
		relation,
		Equal{Left: SequenceLength(x), Right: Integer{Value: 2}},
		Equal{Left: SequenceLength(y), Right: Integer{Value: 1}},
		Equal{Left: SequenceLength(z), Right: Integer{Value: 1}},
	}}
	if checked := Check(Assert(27, New(), conflicting)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}

	nondivisible := Equal{
		Left: Add{Values: []Term[IntSort]{
			IntegerScale{
				Coefficient: NewIntegerValue(2),
				Value:       SequenceLength(x),
			},
			IntegerScale{
				Coefficient: NewIntegerValue(2),
				Value:       SequenceLength(y),
			},
			IntegerScale{
				Coefficient: NewIntegerValue(2),
				Value:       SequenceLength(z),
			},
		}},
		Right: Integer{Value: 7},
	}
	if checked := Check(Assert(28, New(), nondivisible)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("nondivisible result=%T", checked)
	}

	alias := SequenceConst[IntSort](46, "alias")
	aliased := And{Values: []Term[BoolSort]{
		Equal{Left: z, Right: alias},
		Equal{
			Left: Add{Values: []Term[IntSort]{
				SequenceLength(x),
				SequenceLength(y),
				SequenceLength(z),
				SequenceLength(alias),
			}},
			Right: Integer{Value: 6},
		},
		SequenceHasPrefix(x, unit(1)),
		SequenceHasPrefix(y, unit(2)),
		SequenceHasPrefix(z, SequenceConcat(unit(3), unit(4))),
	}}
	aliasedResult, ok := Check(Assert(29, New(), aliased)).(Satisfiable)
	if !ok {
		t.Fatal("alias-canonicalized affine lengths must be satisfiable")
	}
	zValue, zFound = IntegerSequenceModelValue(aliasedResult.Value, z)
	aliasValue, aliasFound := IntegerSequenceModelValue(aliasedResult.Value, alias)
	if !zFound || !aliasFound || zValue.Len() != 2 ||
		aliasValue.Len() != zValue.Len() {
		t.Fatalf(
			"alias lengths=(%d,%v)/(%d,%v)",
			zValue.Len(), zFound, aliasValue.Len(), aliasFound,
		)
	}
}

func TestMultiSymbolAffineLengthIntegerSequenceInequalities(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	prefix := func(values ...int64) Term[SequenceSort[IntSort]] {
		terms := make([]Term[SequenceSort[IntSort]], len(values))
		for index, value := range values {
			terms[index] = unit(value)
		}
		return SequenceConcat(terms...)
	}
	x := SequenceConst[IntSort](47, "x")
	y := SequenceConst[IntSort](48, "y")
	z := SequenceConst[IntSort](49, "z")
	twoSymbol := And{Values: []Term[BoolSort]{
		LessEqual{
			Left: Add{Values: []Term[IntSort]{
				IntegerScale{
					Coefficient: NewIntegerValue(2),
					Value:       SequenceLength(x),
				},
				SequenceLength(y),
			}},
			Right: Integer{Value: 7},
		},
		SequenceHasPrefix(x, prefix(1, 2, 3)),
		SequenceHasSuffix(y, unit(4)),
	}}
	twoResult, ok := Check(Assert(30, New(), twoSymbol)).(Satisfiable)
	if !ok {
		t.Fatal("two-symbol affine inequality must be satisfiable")
	}
	xValue, xFound := IntegerSequenceModelValue(twoResult.Value, x)
	yValue, yFound := IntegerSequenceModelValue(twoResult.Value, y)
	if !xFound || !yFound || 2*xValue.Len()+yValue.Len() > 7 {
		t.Fatalf(
			"two-symbol lengths=(%d,%v)/(%d,%v)",
			xValue.Len(), xFound, yValue.Len(), yFound,
		)
	}

	threeSymbol := And{Values: []Term[BoolSort]{
		Less{
			Left: Add{Values: []Term[IntSort]{
				SequenceLength(x),
				SequenceLength(y),
				SequenceLength(z),
			}},
			Right: Integer{Value: 7},
		},
		SequenceHasPrefix(x, prefix(1, 2)),
		SequenceHasPrefix(y, prefix(3, 4)),
		SequenceHasSuffix(z, prefix(5, 6)),
	}}
	threeResult, ok := Check(Assert(31, New(), threeSymbol)).(Satisfiable)
	if !ok {
		t.Fatal("strict three-symbol affine inequality must be satisfiable")
	}
	xValue, xFound = IntegerSequenceModelValue(threeResult.Value, x)
	yValue, yFound = IntegerSequenceModelValue(threeResult.Value, y)
	zValue, zFound := IntegerSequenceModelValue(threeResult.Value, z)
	if !xFound || !yFound || !zFound ||
		xValue.Len()+yValue.Len()+zValue.Len() >= 7 {
		t.Fatalf(
			"three-symbol lengths=(%d,%v)/(%d,%v)/(%d,%v)",
			xValue.Len(), xFound, yValue.Len(), yFound, zValue.Len(), zFound,
		)
	}

	negativeLast := And{Values: []Term[BoolSort]{
		LessEqual{
			Left: Add{Values: []Term[IntSort]{
				SequenceLength(x),
				SequenceLength(y),
				IntegerScale{
					Coefficient: NewIntegerValue(-2),
					Value:       SequenceLength(z),
				},
			}},
			Right: Integer{Value: -3},
		},
		SequenceHasPrefix(x, unit(1)),
		SequenceHasPrefix(y, unit(2)),
		SequenceHasSuffix(z, unit(3)),
	}}
	negativeResult, ok := Check(Assert(32, New(), negativeLast)).(Satisfiable)
	if !ok {
		t.Fatal("negative final coefficient must be satisfiable")
	}
	xValue, xFound = IntegerSequenceModelValue(negativeResult.Value, x)
	yValue, yFound = IntegerSequenceModelValue(negativeResult.Value, y)
	zValue, zFound = IntegerSequenceModelValue(negativeResult.Value, z)
	if !xFound || !yFound || !zFound ||
		xValue.Len()+yValue.Len()-2*zValue.Len() > -3 {
		t.Fatalf(
			"negative lengths=(%d,%v)/(%d,%v)/(%d,%v)",
			xValue.Len(), xFound, yValue.Len(), yFound, zValue.Len(), zFound,
		)
	}

	conflicting := And{Values: []Term[BoolSort]{
		LessEqual{
			Left: Add{Values: []Term[IntSort]{
				SequenceLength(x),
				SequenceLength(y),
			}},
			Right: Integer{Value: 3},
		},
		Equal{Left: SequenceLength(x), Right: Integer{Value: 2}},
		Equal{Left: SequenceLength(y), Right: Integer{Value: 2}},
	}}
	if checked := Check(Assert(33, New(), conflicting)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}

	system := And{Values: []Term[BoolSort]{
		LessEqual{
			Left: Integer{Value: 6},
			Right: Add{Values: []Term[IntSort]{
				SequenceLength(x),
				SequenceLength(y),
				SequenceLength(z),
			}},
		},
		LessEqual{
			Left: Add{Values: []Term[IntSort]{
				IntegerScale{
					Coefficient: NewIntegerValue(2),
					Value:       SequenceLength(x),
				},
				SequenceLength(y),
				SequenceLength(z),
			}},
			Right: Integer{Value: 8},
		},
		SequenceHasPrefix(x, unit(1)),
		SequenceHasPrefix(y, unit(2)),
		SequenceHasPrefix(z, unit(3)),
	}}
	systemResult, ok := Check(Assert(34, New(), system)).(Satisfiable)
	if !ok {
		t.Fatal("interacting affine inequalities must be satisfiable")
	}
	xValue, xFound = IntegerSequenceModelValue(systemResult.Value, x)
	yValue, yFound = IntegerSequenceModelValue(systemResult.Value, y)
	zValue, zFound = IntegerSequenceModelValue(systemResult.Value, z)
	total := xValue.Len() + yValue.Len() + zValue.Len()
	if !xFound || !yFound || !zFound || total < 6 ||
		2*xValue.Len()+yValue.Len()+zValue.Len() > 8 {
		t.Fatalf(
			"system lengths=(%d,%v)/(%d,%v)/(%d,%v)",
			xValue.Len(), xFound, yValue.Len(), yFound, zValue.Len(), zFound,
		)
	}

	impossibleSystem := And{Values: []Term[BoolSort]{
		LessEqual{
			Left: Add{Values: []Term[IntSort]{
				SequenceLength(x),
				SequenceLength(y),
			}},
			Right: Integer{Value: 2},
		},
		LessEqual{
			Left: Integer{Value: 3},
			Right: Add{Values: []Term[IntSort]{
				SequenceLength(x),
				SequenceLength(y),
			}},
		},
	}}
	if checked := Check(Assert(35, New(), impossibleSystem)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("impossible system result=%T", checked)
	}
}

func TestFourSymbolAffineLengthIntegerSequenceSystems(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	pair := func(left, right int64) Term[SequenceSort[IntSort]] {
		return SequenceConcat(unit(left), unit(right))
	}
	x := SequenceConst[IntSort](60, "x")
	y := SequenceConst[IntSort](61, "y")
	z := SequenceConst[IntSort](62, "z")
	w := SequenceConst[IntSort](63, "w")
	sum := Add{Values: []Term[IntSort]{
		SequenceLength(x),
		SequenceLength(y),
		SequenceLength(z),
		SequenceLength(w),
	}}
	weighted := Add{Values: []Term[IntSort]{
		IntegerScale{
			Coefficient: NewIntegerValue(2),
			Value:       SequenceLength(x),
		},
		SequenceLength(y),
		SequenceLength(z),
		SequenceLength(w),
	}}
	exact := And{Values: []Term[BoolSort]{
		Equal{Left: weighted, Right: Integer{Value: 10}},
		SequenceHasPrefix(x, pair(1, 2)),
		SequenceHasPrefix(y, pair(3, 4)),
		SequenceHasPrefix(z, pair(5, 6)),
		SequenceHasSuffix(w, pair(7, 8)),
	}}
	exactResult, ok := Check(Assert(36, New(), exact)).(Satisfiable)
	if !ok {
		t.Fatal("four-symbol affine equality must be satisfiable")
	}
	var lengths [4]int
	for index, expression := range []Term[SequenceSort[IntSort]]{x, y, z, w} {
		value, found := IntegerSequenceModelValue(exactResult.Value, expression)
		if !found {
			t.Fatalf("missing model index=%d", index)
		}
		lengths[index] = value.Len()
	}
	if 2*lengths[0]+lengths[1]+lengths[2]+lengths[3] != 10 {
		t.Fatalf("exact lengths=%v", lengths)
	}

	system := And{Values: []Term[BoolSort]{
		LessEqual{Left: Integer{Value: 8}, Right: sum},
		LessEqual{Left: weighted, Right: Integer{Value: 10}},
		SequenceHasPrefix(x, pair(1, 2)),
		SequenceHasPrefix(y, pair(3, 4)),
		SequenceHasPrefix(z, pair(5, 6)),
		SequenceHasSuffix(w, pair(7, 8)),
	}}
	systemResult, ok := Check(Assert(37, New(), system)).(Satisfiable)
	if !ok {
		t.Fatal("four-symbol affine system must be satisfiable")
	}
	total := 0
	for index, expression := range []Term[SequenceSort[IntSort]]{x, y, z, w} {
		value, found := IntegerSequenceModelValue(systemResult.Value, expression)
		if !found {
			t.Fatalf("missing system model index=%d", index)
		}
		lengths[index] = value.Len()
		total += value.Len()
	}
	if total < 8 || 2*lengths[0]+lengths[1]+lengths[2]+lengths[3] > 10 {
		t.Fatalf("system lengths=%v", lengths)
	}

	v := SequenceConst[IntSort](64, "v")
	fiveSymbol := Equal{
		Left: Add{Values: []Term[IntSort]{
			sum,
			SequenceLength(v),
		}},
		Right: Integer{Value: 10},
	}
	fiveResult, ok := Check(Assert(38, New(), fiveSymbol)).(Satisfiable)
	if !ok {
		t.Fatal("five-symbol affine equality must be satisfiable")
	}
	total = 0
	for index, expression := range []Term[SequenceSort[IntSort]]{x, y, z, w, v} {
		value, found := IntegerSequenceModelValue(fiveResult.Value, expression)
		if !found {
			t.Fatalf("missing five-symbol model index=%d", index)
		}
		total += value.Len()
	}
	if total != 10 {
		t.Fatalf("five-symbol total=%d", total)
	}

	a := SequenceConst[IntSort](65, "a")
	b := SequenceConst[IntSort](66, "b")
	c := SequenceConst[IntSort](67, "c")
	d := SequenceConst[IntSort](68, "d")
	nineSymbol := Equal{
		Left: Add{Values: []Term[IntSort]{
			sum,
			SequenceLength(v),
			SequenceLength(a),
			SequenceLength(b),
			SequenceLength(c),
			SequenceLength(d),
		}},
		Right: Integer{Value: 10},
	}
	if checked := Check(Assert(39, New(), nineSymbol)); func() bool {
		_, ok := checked.(Unknown)
		return ok
	}() == false {
		t.Fatalf("nine-symbol result=%T", checked)
	}
}

func TestSymbolicIntegerSequenceEqualityClasses(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	x := SequenceConst[IntSort](50, "x")
	y := SequenceConst[IntSort](51, "y")
	z := SequenceConst[IntSort](52, "z")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		Equal{Left: y, Right: z},
		SequenceHasPrefix(x, unit(1)),
		SequenceContains(y, unit(2)),
		SequenceHasSuffix(z, unit(3)),
		Equal{Left: SequenceLength(y), Right: Integer{Value: 3}},
	}}
	checked := Check(Assert(26, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	for name, expression := range map[string]Term[SequenceSort[IntSort]]{
		"x": x,
		"y": y,
		"z": z,
	} {
		value, found := IntegerSequenceModelValue(result.Value, expression)
		if !found || value.Len() != 3 {
			t.Fatalf("%s len=(%d,%v)", name, value.Len(), found)
		}
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	ground := SequenceConcat(unit(4), unit(5))
	assigned := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		Equal{Left: y, Right: ground},
	}}
	assignedResult, ok := Check(Assert(27, New(), assigned)).(Satisfiable)
	if !ok {
		t.Fatalf("aliased assignment result=%T", Check(Assert(27, New(), assigned)))
	}
	if value, found := IntegerSequenceModelValue(assignedResult.Value, x); !found || value.Len() != 2 {
		t.Fatalf("assigned x len=(%d,%v)", value.Len(), found)
	}

	conflicting := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: y},
		Equal{Left: x, Right: unit(1)},
		Equal{Left: y, Right: unit(2)},
	}}
	if checked := Check(Assert(28, New(), conflicting)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}

	aliasOnly := Equal{Left: x, Right: y}
	aliasResult, ok := Check(Assert(29, New(), aliasOnly)).(Satisfiable)
	if !ok {
		t.Fatal("bare alias must construct a shared model")
	}
	if left, leftOK := IntegerSequenceModelValue(aliasResult.Value, x); !leftOK || left.Len() != 0 {
		t.Fatalf("alias-only x len=(%d,%v)", left.Len(), leftOK)
	}
}

func TestTwoSymbolAffineIntegerSequenceLengths(t *testing.T) {
	unit := func(value int64) Term[SequenceSort[IntSort]] {
		return SequenceUnit[IntSort](Integer{Value: value})
	}
	x := SequenceConst[IntSort](60, "x")
	y := SequenceConst[IntSort](61, "y")
	relation := Equal{
		Left: Add{Values: []Term[IntSort]{
			IntegerScale{
				Coefficient: NewIntegerValue(2),
				Value:       SequenceLength(x),
			},
			SequenceLength(y),
		}},
		Right: Integer{Value: 7},
	}
	formula := And{Values: []Term[BoolSort]{
		relation,
		SequenceHasPrefix(x, unit(1)),
		SequenceHasSuffix(y, unit(3)),
	}}
	checked := Check(Assert(30, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	xValue, xFound := IntegerSequenceModelValue(result.Value, x)
	yValue, yFound := IntegerSequenceModelValue(result.Value, y)
	if !xFound || !yFound || 2*xValue.Len()+yValue.Len() != 7 {
		t.Fatalf("lengths=(%d,%v)/(%d,%v)", xValue.Len(), xFound, yValue.Len(), yFound)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	conflicting := And{Values: []Term[BoolSort]{
		relation,
		Equal{Left: SequenceLength(x), Right: Integer{Value: 2}},
		Equal{Left: SequenceLength(y), Right: Integer{Value: 2}},
	}}
	if checked := Check(Assert(31, New(), conflicting)); func() bool {
		_, ok := checked.(Unsatisfiable)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}
}
