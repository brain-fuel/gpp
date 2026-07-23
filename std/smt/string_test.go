package smt

import (
	"strings"
	"testing"
)

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

func TestStringRegexSynthesizesSharedConstraintWitness(t *testing.T) {
	x := StringConst(1, "x")
	a := StringToRegex(StringVal("a"))
	b := StringToRegex(StringVal("b"))
	c := StringToRegex(StringVal("c"))
	formula := And{Values: []Term[BoolSort]{
		StringInRegex(x, UnionRegex(a, b)),
		StringInRegex(x, UnionRegex(b, c)),
		Not{Value: StringInRegex(x, a)},
	}}
	checked := Check(Assert(12, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T (%#v)", checked, checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "b" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
}

func TestStringRegexProvesEmptySingletonIntersection(t *testing.T) {
	x := StringConst(1, "x")
	formula := And{Values: []Term[BoolSort]{
		StringInRegex(x, StringToRegex(StringVal("a"))),
		StringInRegex(x, StringToRegex(StringVal("b"))),
	}}
	checked := Check(Assert(13, New(), formula))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("result=%T", checked)
	}
}

func TestStringRegexBooleanBranchModels(t *testing.T) {
	x := StringConst(1, "x")
	a := StringInRegex(x, StringToRegex(StringVal("a")))
	b := StringInRegex(x, StringToRegex(StringVal("b")))
	c := StringInRegex(x, StringToRegex(StringVal("c")))

	choice := And{Values: []Term[BoolSort]{
		Or{Values: []Term[BoolSort]{a, b}},
		Not{Value: a},
	}}
	checked := Check(Assert(14, New(), choice))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("choice result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "b" {
		t.Fatalf("choice x=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, choice); !found || !valid {
		t.Fatalf("choice formula=(%v,%v)", valid, found)
	}

	impossibleImplication := And{Values: []Term[BoolSort]{
		a,
		Implies{Left: a, Right: b},
	}}
	checked = Check(Assert(15, New(), impossibleImplication))
	if _, unsat := checked.(Unsatisfiable); !unsat {
		t.Fatalf("implication result=%T", checked)
	}

	impossibleEquivalence := And{Values: []Term[BoolSort]{
		Or{Values: []Term[BoolSort]{a, b}},
		Iff{Left: a, Right: b},
	}}
	checked = Check(Assert(16, New(), impossibleEquivalence))
	if _, unsat := checked.(Unsatisfiable); !unsat {
		t.Fatalf("equivalence result=%T", checked)
	}

	conditional := And{Values: []Term[BoolSort]{
		Not{Value: a},
		If[BoolSort]{Condition: a, Then: c, Else: b},
	}}
	checked = Check(Assert(17, New(), conditional))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("conditional result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "b" {
		t.Fatalf("conditional x=(%q,%v)", actual, found)
	}
}

func TestStringSingleUnknownWordEquation(t *testing.T) {
	x := StringConst(1, "x")
	equation := Equal{
		Left:  StringConcat(StringVal("go-"), x, StringVal("!")),
		Right: StringVal("go-forge!"),
	}
	checked := Check(Assert(18, New(), equation))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "forge" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, equation); !found || !valid {
		t.Fatalf("equation=(%v,%v)", valid, found)
	}

	impossible := Equal{
		Left:  StringConcat(StringVal("go-"), x),
		Right: StringVal("no-forge"),
	}
	checked = Check(Assert(19, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestStringUniquelyDelimitedWordEquation(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	equation := Equal{
		Left: StringConcat(
			StringVal("["), x, StringVal("]"),
			y, StringVal("!"),
		),
		Right: StringVal("[go]forge!"),
	}
	checked := Check(Assert(22, New(), equation))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "go" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "forge" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, equation); !found || !valid {
		t.Fatalf("equation=(%v,%v)", valid, found)
	}

	conflict := And{Values: []Term[BoolSort]{
		equation,
		Equal{Left: x, Right: StringVal("not-go")},
	}}
	checked = Check(Assert(23, New(), conflict))
	if _, unsat := checked.(Unsatisfiable); !unsat {
		t.Fatalf("conflict result=%T", checked)
	}

	ambiguous := Equal{
		Left:  StringConcat(StringVal("["), x, StringVal("]"), y, StringVal("!")),
		Right: StringVal("[a]b]c!"),
	}
	checked = Check(Assert(24, New(), ambiguous))
	ambiguousResult, sat := checked.(Satisfiable)
	if !sat {
		t.Fatalf("ambiguous result=%T", checked)
	}
	if actual, found := StringModelValue(ambiguousResult.Value, x); !found || actual != "a" {
		t.Fatalf("ambiguous x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(ambiguousResult.Value, y); !found || actual != "b]c" {
		t.Fatalf("ambiguous y=(%q,%v)", actual, found)
	}

	adjacent := Equal{
		Left:  StringConcat(x, y),
		Right: StringVal("forge"),
	}
	checked = Check(Assert(25, New(), adjacent))
	adjacentResult, sat := checked.(Satisfiable)
	if !sat {
		t.Fatalf("adjacent result=%T", checked)
	}
	if actual, found := StringModelValue(adjacentResult.Value, x); !found || actual != "" {
		t.Fatalf("adjacent x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(adjacentResult.Value, y); !found || actual != "forge" {
		t.Fatalf("adjacent y=(%q,%v)", actual, found)
	}
}

func TestCompactStringWordEquationModel(t *testing.T) {
	pattern := CompactStringPattern{
		Count:       4,
		SymbolIDs:   [4]int{1, 2, 3, 4},
		SymbolNames: [4]string{"x", "y", "z", "w"},
		Delimiters:  [5]string{"[", "]", "{", "}", "!"},
	}
	equation := CompactStringWordEquation{
		Pattern: pattern,
		Target:  "[go]forge{typed}solver!",
	}
	checked := Check(Assert(25, New(), equation))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := CompactStringModelValue(result.Value, CompactStringSymbolTerm(1, "x")); !found || actual != "go" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := CompactStringModelValue(result.Value, CompactStringSymbolTerm(2, "y")); !found || actual != "forge" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if actual, found := CompactStringModelValue(result.Value, CompactStringSymbolTerm(3, "z")); !found || actual != "typed" {
		t.Fatalf("z=(%q,%v)", actual, found)
	}
	if actual, found := CompactStringModelValue(result.Value, CompactStringSymbolTerm(4, "w")); !found || actual != "solver" {
		t.Fatalf("w=(%q,%v)", actual, found)
	}
	if valid, found := CompactStringWordEquationValue(result.Value, equation); !found || !valid {
		t.Fatalf("equation=(%v,%v)", valid, found)
	}
}

func TestRepeatedSymbolWordEquation(t *testing.T) {
	x := StringConst(1, "x")
	for _, test := range []struct {
		name   string
		left   Term[StringSort]
		target string
		value  string
		sat    bool
	}{
		{
			name: "adjacent", left: StringConcat(x, x),
			target: "abab", value: "ab", sat: true,
		},
		{
			name: "delimited", left: StringConcat(x, StringVal("-"), x),
			target: "go-go", value: "go", sat: true,
		},
		{
			name: "unicode", left: StringConcat(x, x),
			target: "🙂🙂", value: "🙂", sat: true,
		},
		{
			name: "inconsistent", left: StringConcat(x, StringVal("-"), x),
			target: "go-rust", sat: false,
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			equation := Equal{Left: test.left, Right: StringVal(test.target)}
			checked := Check(Assert(26, New(), equation))
			if !test.sat {
				if _, ok := checked.(Unsatisfiable); !ok {
					t.Fatalf("result=%T", checked)
				}
				return
			}
			result, ok := checked.(Satisfiable)
			if !ok {
				t.Fatalf("result=%T", checked)
			}
			if actual, found := StringModelValue(result.Value, x); !found || actual != test.value {
				t.Fatalf("x=(%q,%v)", actual, found)
			}
			if valid, found := BoolValue(result.Value, equation); !found || !valid {
				t.Fatalf("equation=(%v,%v)", valid, found)
			}
		})
	}
}

func TestRepeatedSymbolWordEquationSearchLimit(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	equation := Equal{
		Left:  StringConcat(x, y, x, y),
		Right: StringVal(strings.Repeat("a", 96) + "b"),
	}
	checked := Check(Assert(27, New(), equation))
	result, ok := checked.(Unknown)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if limit, ok := result.Reason.(ResourceLimit); !ok || limit.Limit != compactStringWordEquationSearchLimit {
		t.Fatalf("reason=%#v", result.Reason)
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

func TestCompactStringBooleanFormulaModel(t *testing.T) {
	x := CompactStringSymbolTerm(1, "x")
	a, ok := CompactStringRegexLiteralFormula(x, "a")
	if !ok {
		t.Fatal("expected compact a membership")
	}
	b, _ := CompactStringRegexLiteralFormula(x, "b")
	c, _ := CompactStringRegexLiteralFormula(x, "c")
	aOrB, _ := CompactStringBooleanOrFormula(a, b)
	notA, _ := CompactStringBooleanNotFormula(a)
	notB, _ := CompactStringBooleanNotFormula(b)
	notC, _ := CompactStringBooleanNotFormula(c)
	implication, _ := CompactStringBooleanOrFormula(notB, notC)
	aAndC, _ := CompactStringBooleanAndFormula(a, c)
	notAAndB, _ := CompactStringBooleanAndFormula(notA, b)
	conditional, _ := CompactStringBooleanOrFormula(aAndC, notAAndB)
	formula, _ := CompactStringBooleanAndFormula(aOrB, notA)
	formula, _ = CompactStringBooleanAndFormula(formula, implication)
	formula, ok = CompactStringBooleanAndFormula(formula, conditional)
	if !ok {
		t.Fatal("expected formula to fit the compact postfix arena")
	}

	checked := Check(Assert(20, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if value, found := CompactStringModelValue(result.Value, x); !found || value != "b" {
		t.Fatalf("x=(%q,%v)", value, found)
	}
	if valid, found := CompactStringBooleanValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	contradiction, _ := CompactStringBooleanAndFormula(a, notA)
	checked = Check(Assert(21, New(), contradiction))
	if _, unsat := checked.(Unsatisfiable); !unsat {
		t.Fatalf("contradiction result=%T", checked)
	}
}
