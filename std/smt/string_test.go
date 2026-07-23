package smt

import "testing"

func TestStringGroundOperations(t *testing.T) {
	value := StringConcat(StringVal("Go"), StringVal("+"), StringVal("🙂"))
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: value, Right: StringVal("Go+🙂")},
		Equal{Left: StringLength(value), Right: Integer{Value: 4}},
		StringContains(value, StringVal("+")),
		StringHasPrefix(value, StringVal("Go")),
		StringHasSuffix(value, StringVal("🙂")),
	}}
	checked := Check(Assert(1, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T (%#v)", checked, checked)
	}
	if actual, found := StringModelValue(result.Value, value); !found || actual != "Go+🙂" {
		t.Fatalf("value=(%q,%v)", actual, found)
	}
}

func TestStringIndexedOperationsUseUnicodeCodePoints(t *testing.T) {
	value := StringVal("a🙂bc🙂")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: StringAt(value, Integer{Value: 1}), Right: StringVal("🙂")},
		Equal{Left: StringAt(value, Integer{Value: -1}), Right: StringVal("")},
		Equal{Left: StringAt(value, Integer{Value: 99}), Right: StringVal("")},
		Equal{Left: StringSubstring(value, Integer{Value: 1}, Integer{Value: 3}), Right: StringVal("🙂bc")},
		Equal{Left: StringSubstring(value, Integer{Value: 4}, Integer{Value: 99}), Right: StringVal("🙂")},
		Equal{Left: StringSubstring(value, Integer{Value: -1}, Integer{Value: 2}), Right: StringVal("")},
		Equal{Left: StringIndexOf(value, StringVal("🙂"), Integer{Value: 2}), Right: Integer{Value: 4}},
		Equal{Left: StringIndexOf(value, StringVal(""), Integer{Value: 5}), Right: Integer{Value: 5}},
		Equal{Left: StringIndexOf(value, StringVal("x"), Integer{Value: 0}), Right: Integer{Value: -1}},
		Equal{Left: StringReplace(value, StringVal("🙂"), StringVal("!")), Right: StringVal("a!bc🙂")},
		Equal{Left: StringReplace(StringVal("ab"), StringVal(""), StringVal("!")), Right: StringVal("!ab")},
	}}
	if _, ok := Check(Assert(6, New(), formula)).(Satisfiable); !ok {
		t.Fatalf("result=%T", Check(Assert(6, New(), formula)))
	}
}

func TestStringConversionsAndReplaceAll(t *testing.T) {
	huge, err := ParseIntegerValue("123456789012345678901234567890")
	if err != nil {
		t.Fatal(err)
	}
	surrogate, ok := EncodeStringCodePoint(0xd800)
	if !ok {
		t.Fatal("expected SMT surrogate code point")
	}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: StringReplaceAll(StringVal("aaaa"), StringVal("aa"), StringVal("b")), Right: StringVal("bb")},
		Equal{Left: StringReplaceAll(StringVal("ab"), StringVal(""), StringVal("x")), Right: StringVal("ab")},
		Equal{Left: StringToInt(StringVal("0012")), Right: Integer{Value: 12}},
		Equal{Left: StringToInt(StringVal("-12")), Right: Integer{Value: -1}},
		Equal{Left: StringToInt(StringVal(huge.String())), Right: IntegerTerm(huge)},
		Equal{Left: IntToString(IntegerTerm(huge)), Right: StringVal(huge.String())},
		Equal{Left: IntToString(Integer{Value: -1}), Right: StringVal("")},
		Equal{Left: StringToCode(StringVal(surrogate)), Right: Integer{Value: 0xd800}},
		Equal{Left: StringFromCode(Integer{Value: 0xd800}), Right: StringVal(surrogate)},
		Equal{Left: StringFromCode(Integer{Value: 0x30000}), Right: StringVal("")},
		StringIsDigit(StringVal("7")),
		Not{Value: StringIsDigit(StringVal("٧"))},
		Not{Value: StringIsDigit(StringVal("77"))},
	}}
	if _, ok := Check(Assert(7, New(), formula)).(Satisfiable); !ok {
		t.Fatalf("result=%T", Check(Assert(7, New(), formula)))
	}
}

func TestStringRegexLanguageOperations(t *testing.T) {
	a := StringToRegex(StringVal("a"))
	b := StringToRegex(StringVal("b"))
	ab := ConcatRegex(a, b)
	letter := StringRangeRegex(StringVal("a"), StringVal("z"))
	aOrB := UnionRegex(a, b)
	onlyA := IntersectRegex(aOrB, a)
	notB := DifferenceRegex(aOrB, b)
	notA := ComplementRegex(a)
	formula := And{Values: []Term[BoolSort]{
		StringInRegex(StringVal("ab"), ab),
		StringInRegex(StringVal("abba"), StarRegex(aOrB)),
		StringInRegex(StringVal("ab"), PlusRegex(letter)),
		StringInRegex(StringVal(""), OptionalRegex(a)),
		StringInRegex(StringVal("a"), OptionalRegex(a)),
		StringInRegex(StringVal("aaa"), LoopRegex(2, 4, a)),
		StringInRegex(StringVal("a"), onlyA),
		StringInRegex(StringVal("a"), notB),
		StringInRegex(StringVal("b"), notA),
		StringInRegex(StringVal("anything"), FullRegex[StringSort]()),
		StringInRegex(StringVal("x"), AllCharRegex[StringSort]()),
		Not{Value: StringInRegex(StringVal(""), AllCharRegex[StringSort]())},
		Not{Value: StringInRegex(StringVal("a"), EmptyRegex[StringSort]())},
		Not{Value: StringInRegex(StringVal("aaaaa"), LoopRegex(2, 4, a))},
	}}
	if _, ok := Check(Assert(8, New(), formula)).(Satisfiable); !ok {
		t.Fatalf("result=%T", Check(Assert(8, New(), formula)))
	}
}

func TestStringRegexSynthesizesSymbolicWitnesses(t *testing.T) {
	x := StringConst(1, "x")
	language := ConcatRegex(
		StringToRegex(StringVal("go-")),
		LoopRegex(2, 4, StringRangeRegex(StringVal("a"), StringVal("z"))),
	)
	checked := Check(Assert(9, New(), StringInRegex(x, language)))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("positive result=%T (%#v)", checked, checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "go-aa" {
		t.Fatalf("positive x=(%q,%v)", actual, found)
	}

	y := StringConst(2, "y")
	negative := Not{Value: StringInRegex(y, StringToRegex(StringVal("")))}
	checked = Check(Assert(10, New(), negative))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("negative result=%T (%#v)", checked, checked)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual == "" {
		t.Fatalf("negative y=(%q,%v)", actual, found)
	}
}

func TestStringRegexRejectsForcedSymbolContradiction(t *testing.T) {
	x := StringConst(1, "x")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: StringVal("a")},
		StringInRegex(x, StringToRegex(StringVal("b"))),
	}}
	checked := Check(Assert(11, New(), formula))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("result=%T", checked)
	}
}

func TestStringSymbolModel(t *testing.T) {
	x := StringConst(1, "x")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: StringVal("goforge")},
		StringHasPrefix(x, StringVal("go")),
		StringHasSuffix(x, StringVal("forge")),
	}}
	checked := Check(Assert(2, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T (%#v)", checked, checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "goforge" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
}

func TestStringDisequalitySynthesizesDistinctValues(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	checked := Check(Assert(3, New(), Not{Value: Equal{Left: x, Right: y}}))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T (%#v)", checked, checked)
	}
	left, leftOK := StringModelValue(result.Value, x)
	right, rightOK := StringModelValue(result.Value, y)
	if !leftOK || !rightOK || left == right {
		t.Fatalf("x=(%q,%v), y=(%q,%v)", left, leftOK, right, rightOK)
	}
}

func TestStringGroundContradiction(t *testing.T) {
	formula := StringHasPrefix(StringVal("forge"), StringVal("go"))
	if _, ok := Check(Assert(4, New(), formula)).(Unsatisfiable); !ok {
		t.Fatal("expected ground string contradiction to be unsatisfiable")
	}
}

func TestStringAssumptionModel(t *testing.T) {
	x := StringConst(1, "x")
	checked := CheckAssuming(New(), Equal{Left: x, Right: StringVal("assumed")})
	result, ok := checked.(AssumptionsSatisfiable)
	if !ok {
		t.Fatalf("result=%T (%#v)", checked, checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "assumed" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
}

func BenchmarkStringQFSLIA(b *testing.B) {
	x := StringConst(1, "x")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: x, Right: StringConcat(StringVal("go-"), StringVal("forge"))},
		Equal{Left: StringLength(x), Right: Integer{Value: 8}},
		StringContains(x, StringVal("-")),
		StringHasPrefix(x, StringVal("go")),
		StringHasSuffix(x, StringVal("forge")),
	}}
	b.ReportAllocs()
	for index := 0; index < b.N; index++ {
		if _, ok := Check(Assert(index+1, New(), formula)).(Satisfiable); !ok {
			b.Fatal("expected satisfiable string workload")
		}
	}
}

func TestCompactStringSystemModel(t *testing.T) {
	x := CompactStringSymbolTerm(1, "x")
	literal := CompactStringLiteralTerm("go-forge")
	var system CompactStringSystem
	system = AppendCompactStringRelation(system, CompactStringRelation{Kind: CompactStringEqual, Left: x, Right: literal})
	system = AppendCompactStringRelation(system, CompactStringRelation{Kind: CompactStringLengthEqual, Left: x, Integer: 8})
	system = AppendCompactStringRelation(system, CompactStringRelation{Kind: CompactStringContains, Left: x, Right: CompactStringLiteralTerm("-")})
	system = AppendCompactStringRelation(system, CompactStringRelation{Kind: CompactStringPrefix, Left: x, Right: CompactStringLiteralTerm("go")})
	system = AppendCompactStringRelation(system, CompactStringRelation{Kind: CompactStringSuffix, Left: x, Right: CompactStringLiteralTerm("forge")})
	term := CompactStringAssertions(system)
	result, ok := Check(Assert(5, New(), term)).(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(5, New(), term)))
	}
	if value, found := StringModelValue(result.Value, StringConst(1, "x")); !found || value != "go-forge" {
		t.Fatalf("x=(%q,%v)", value, found)
	}
	if valid, found := BoolValue(result.Value, term); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
}
