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
	invalid := StringVal("\xe2x")
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
		Equal{Left: StringAt(invalid, Integer{Value: 0}), Right: StringVal(string([]rune{'\uFFFD'}))},
		Equal{Left: StringSubstring(invalid, Integer{Value: 0}, Integer{Value: 2}), Right: StringVal(string([]rune{'\uFFFD', 'x'}))},
		Equal{Left: StringIndexOf(invalid, StringVal("\xe2"), Integer{Value: 0}), Right: Integer{Value: -1}},
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

	secondSplit := And{Values: []Term[BoolSort]{
		ambiguous,
		Equal{Left: x, Right: StringVal("a]b")},
	}}
	checked = Check(Assert(25, New(), secondSplit))
	secondResult, sat := checked.(Satisfiable)
	if !sat {
		t.Fatalf("second split result=%T", checked)
	}
	if actual, found := StringModelValue(secondResult.Value, y); !found || actual != "c" {
		t.Fatalf("second split y=(%q,%v)", actual, found)
	}

	impossibleSplit := And{Values: []Term[BoolSort]{
		ambiguous,
		Equal{Left: x, Right: StringVal("wrong")},
	}}
	checked = Check(Assert(26, New(), impossibleSplit))
	if _, unsat := checked.(Unsatisfiable); !unsat {
		t.Fatalf("impossible split result=%T", checked)
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

func TestWordEquationLengthInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	equation := Equal{Left: StringConcat(x, y), Right: StringVal("forge")}
	formula := And{Values: []Term[BoolSort]{
		equation,
		Equal{Left: StringLength(x), Right: Integer{Value: 3}},
	}}
	checked := Check(Assert(28, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "for" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "ge" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	unicode := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("🙂a")},
		Equal{Left: StringLength(x), Right: Integer{Value: 1}},
	}}
	checked = Check(Assert(29, New(), unicode))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("unicode result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "🙂" {
		t.Fatalf("unicode x=(%q,%v)", actual, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		equation,
		Equal{Left: StringLength(x), Right: Integer{Value: 10}},
	}}
	checked = Check(Assert(30, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestWordEquationLengthInequalityInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	equation := Equal{Left: StringConcat(x, y), Right: StringVal("forge")}
	formula := And{Values: []Term[BoolSort]{
		equation,
		Less{Left: Integer{Value: 1}, Right: StringLength(x)},
		LessEqual{Left: StringLength(x), Right: Integer{Value: 3}},
	}}
	checked := Check(Assert(31, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "fo" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "rge" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	unicode := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("🙂a")},
		Less{Left: Integer{Value: 0}, Right: StringLength(x)},
		LessEqual{Left: StringLength(x), Right: Integer{Value: 1}},
	}}
	checked = Check(Assert(32, New(), unicode))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("unicode result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "🙂" {
		t.Fatalf("unicode x=(%q,%v)", actual, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		equation,
		Less{Left: Integer{Value: 5}, Right: StringLength(x)},
	}}
	checked = Check(Assert(33, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestWordEquationRelationalLengthInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	equalLength := Equal{Left: StringLength(x), Right: StringLength(y)}
	equalFormula := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abcd")},
		equalLength,
	}}
	checked := Check(Assert(33, New(), equalFormula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("equal result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "ab" {
		t.Fatalf("equal x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "cd" {
		t.Fatalf("equal y=(%q,%v)", actual, found)
	}

	ordered := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abc")},
		Or{Values: []Term[BoolSort]{
			equalLength,
			Less{Left: StringLength(y), Right: StringLength(x)},
		}},
	}}
	checked = Check(Assert(34, New(), ordered))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("ordered result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "ab" {
		t.Fatalf("ordered x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "c" {
		t.Fatalf("ordered y=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, ordered); !found || !valid {
		t.Fatalf("ordered formula=(%v,%v)", valid, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abc")},
		equalLength,
	}}
	checked = Check(Assert(35, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestWordEquationAffineLengthInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	weighted := Add{Values: []Term[IntSort]{
		IntegerScale{Coefficient: NewIntegerValue(2), Value: StringLength(x)},
		StringLength(y),
	}}
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abcd")},
		Equal{Left: weighted, Right: Integer{Value: 6}},
	}}
	checked := Check(Assert(36, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "ab" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "cd" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	ordered := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abc")},
		Less{
			Left:  Integer{Value: 0},
			Right: Subtract{Left: StringLength(x), Right: StringLength(y)},
		},
	}}
	checked = Check(Assert(37, New(), ordered))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("ordered result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "ab" {
		t.Fatalf("ordered x=(%q,%v)", actual, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abc")},
		Equal{
			Left:  Add{Values: []Term[IntSort]{StringLength(x), StringLength(y)}},
			Right: Integer{Value: 4},
		},
	}}
	checked = Check(Assert(38, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestWordEquationIntegerStringOperationInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	indexFormula := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abc")},
		Equal{
			Left:  StringIndexOf(x, StringVal("b"), Integer{Value: 0}),
			Right: Integer{Value: 1},
		},
	}}
	checked := Check(Assert(39, New(), indexFormula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("index result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "ab" {
		t.Fatalf("index x=(%q,%v)", actual, found)
	}

	toIntegerFormula := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("12z")},
		Equal{Left: StringToInt(x), Right: Integer{Value: 12}},
	}}
	checked = Check(Assert(40, New(), toIntegerFormula))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("to-int result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "12" {
		t.Fatalf("to-int x=(%q,%v)", actual, found)
	}

	toCodeFormula := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("a🙂")},
		Equal{Left: StringToCode(x), Right: Integer{Value: 97}},
	}}
	checked = Check(Assert(41, New(), toCodeFormula))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("to-code result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
		t.Fatalf("to-code x=(%q,%v)", actual, found)
	}

	const digits = "1234567890123456789012345678901234567890"
	exact, err := ParseIntegerValue(digits)
	if err != nil {
		t.Fatal(err)
	}
	wide := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal(digits + "!")},
		Equal{Left: StringToInt(x), Right: IntegerTerm(exact)},
	}}
	checked = Check(Assert(42, New(), wide))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("wide result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != digits {
		t.Fatalf("wide x=(%q,%v)", actual, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abc")},
		Equal{Left: StringToCode(x), Right: Integer{Value: 122}},
	}}
	checked = Check(Assert(43, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestWordEquationDerivedStringOperationInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	cases := []struct {
		name      string
		target    string
		predicate Term[BoolSort]
		want      string
	}{
		{
			name:   "at",
			target: "a🙂c",
			predicate: Equal{
				Left: StringAt(x, Integer{Value: 1}), Right: StringVal("🙂"),
			},
			want: "a🙂",
		},
		{
			name:   "substring",
			target: "abcd",
			predicate: Equal{
				Left:  StringSubstring(x, Integer{Value: 1}, Integer{Value: 2}),
				Right: StringVal("bc"),
			},
			want: "abc",
		},
		{
			name:   "replace",
			target: "abc",
			predicate: Equal{
				Left:  StringReplace(x, StringVal("a"), StringVal("z")),
				Right: StringVal("z"),
			},
			want: "a",
		},
		{
			name:   "replace-all",
			target: "aab",
			predicate: Equal{
				Left:  StringReplaceAll(x, StringVal("a"), StringVal("z")),
				Right: StringVal("zz"),
			},
			want: "aa",
		},
		{
			name:   "from-int",
			target: "12x",
			predicate: Equal{
				Left:  StringAt(x, Integer{Value: 0}),
				Right: StringAt(IntToString(Integer{Value: 12}), Integer{Value: 0}),
			},
			want: "1",
		},
		{
			name:   "from-code",
			target: "a🙂",
			predicate: Equal{
				Left:  StringAt(x, Integer{Value: 0}),
				Right: StringFromCode(Integer{Value: 97}),
			},
			want: "a",
		},
	}
	for index, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			formula := And{Values: []Term[BoolSort]{
				Equal{Left: StringConcat(x, y), Right: StringVal(test.target)},
				test.predicate,
			}}
			checked := Check(Assert(44+index, New(), formula))
			result, ok := checked.(Satisfiable)
			if !ok {
				t.Fatalf("result=%T", checked)
			}
			if actual, found := StringModelValue(result.Value, x); !found || actual != test.want {
				t.Fatalf("x=(%q,%v), want %q", actual, found, test.want)
			}
			if valid, found := BoolValue(result.Value, formula); !found || !valid {
				t.Fatalf("formula=(%v,%v)", valid, found)
			}
		})
	}

	impossible := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abc")},
		Equal{Left: StringAt(x, Integer{Value: 4}), Right: StringVal("z")},
	}}
	checked := Check(Assert(50, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestGroundIndexedStringEqualities(t *testing.T) {
	x := StringConst(1, "x")
	t.Run("at canonical model", func(t *testing.T) {
		formula := Equal{
			Left: StringAt(x, Integer{Value: 1}), Right: StringVal("🙂"),
		}
		checked := Check(Assert(51, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "a🙂" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("overlapping substring and at", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{
				Left:  StringSubstring(x, Integer{Value: 1}, Integer{Value: 3}),
				Right: StringVal("b🙂c"),
			},
			Equal{
				Left: StringAt(x, Integer{Value: 2}), Right: StringVal("🙂"),
			},
		}}
		checked := Check(Assert(52, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "ab🙂c" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("truncated substring fixes length", func(t *testing.T) {
		formula := Equal{
			Left:  StringSubstring(x, Integer{Value: 2}, Integer{Value: 8}),
			Right: StringVal("go"),
		}
		checked := Check(Assert(53, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "aago" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("conflicting placement", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{Left: StringAt(x, Integer{Value: 0}), Right: StringVal("a")},
			Equal{Left: StringAt(x, Integer{Value: 0}), Right: StringVal("b")},
		}}
		checked := Check(Assert(54, New(), formula))
		if _, ok := checked.(Unsatisfiable); !ok {
			t.Fatalf("result=%T", checked)
		}
	})

	t.Run("empty result upper bound", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{Left: StringAt(x, Integer{Value: 1}), Right: StringVal("")},
			Equal{Left: StringAt(x, Integer{Value: 2}), Right: StringVal("c")},
		}}
		checked := Check(Assert(55, New(), formula))
		if _, ok := checked.(Unsatisfiable); !ok {
			t.Fatalf("result=%T", checked)
		}
	})

	t.Run("reversed ground derived result", func(t *testing.T) {
		formula := Equal{
			Left:  StringFromCode(Integer{Value: 97}),
			Right: StringAt(x, Integer{Value: 0}),
		}
		checked := Check(Assert(56, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})
}

func TestGroundStringReplaceEqualities(t *testing.T) {
	x := StringConst(1, "x")
	t.Run("canonical unchanged preimage", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplace(x, StringVal("a"), StringVal("z")),
			Right: StringVal("z"),
		}
		checked := Check(Assert(57, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "z" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("forced replacement preimage", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplace(x, StringVal("a"), StringVal("z")),
			Right: StringVal("za"),
		}
		checked := Check(Assert(58, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "aa" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("empty source", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplace(x, StringVal(""), StringVal("!")),
			Right: StringVal("!ab"),
		}
		checked := Check(Assert(59, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "ab" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("constraint intersection", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{
				Left:  StringReplace(x, StringVal("a"), StringVal("z")),
				Right: StringVal("z"),
			},
			Equal{
				Left:  StringReplace(x, StringVal("b"), StringVal("y")),
				Right: StringVal("a"),
			},
		}}
		checked := Check(Assert(60, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("unicode and reversed equality", func(t *testing.T) {
		formula := Equal{
			Left:  StringVal("go!🙂"),
			Right: StringReplace(x, StringVal("🙂"), StringVal("!")),
		}
		checked := Check(Assert(61, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "go🙂🙂" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("incompatible targets", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{
				Left:  StringReplace(x, StringVal("a"), StringVal("z")),
				Right: StringVal("z"),
			},
			Equal{
				Left:  StringReplace(x, StringVal("a"), StringVal("z")),
				Right: StringVal("q"),
			},
		}}
		checked := Check(Assert(62, New(), formula))
		if _, ok := checked.(Unsatisfiable); !ok {
			t.Fatalf("result=%T", checked)
		}
	})

	t.Run("no inverse", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplaceAll(x, StringVal("a"), StringVal("z")),
			Right: StringVal("a"),
		}
		checked := Check(Assert(74, New(), formula))
		if _, ok := checked.(Unsatisfiable); !ok {
			t.Fatalf("result=%T", checked)
		}
	})

	t.Run("deletion inverse", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplaceAll(x, StringVal("ab"), StringVal("")),
			Right: StringVal("ab"),
		}
		checked := Check(Assert(75, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "aabb" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("impossible deletion inverse", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplaceAll(x, StringVal("a"), StringVal("")),
			Right: StringVal("a"),
		}
		checked := Check(Assert(76, New(), formula))
		if _, ok := checked.(Unsatisfiable); !ok {
			t.Fatalf("result=%T", checked)
		}
	})

	t.Run("filtered cyclic deletion selects longer preimage", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{
				Left:  StringReplaceAll(x, StringVal("ab"), StringVal("")),
				Right: StringVal("ab"),
			},
			Equal{Left: StringLength(x), Right: Integer{Value: 6}},
		}}
		checked := Check(Assert(77, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "aababb" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("forced cyclic deletion contradiction", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{
				Left:  StringReplaceAll(x, StringVal("ab"), StringVal("")),
				Right: StringVal("ab"),
			},
			Equal{Left: x, Right: StringVal("q")},
		}}
		checked := Check(Assert(79, New(), formula))
		if _, ok := checked.(Unsatisfiable); !ok {
			t.Fatalf("result=%T", checked)
		}
	})

	t.Run("deletion state limit", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplaceAll(x, StringVal("a"), StringVal("")),
			Right: StringVal(strings.Repeat("a", compactStringWordEquationSearchLimit)),
		}
		checked := Check(Assert(78, New(), formula))
		unknown, ok := checked.(Unknown)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if _, ok := unknown.Reason.(ResourceLimit); !ok {
			t.Fatalf("reason=%T", unknown.Reason)
		}
	})
}

func TestGroundStringReplaceAllEqualities(t *testing.T) {
	x := StringConst(1, "x")
	t.Run("overlapping inverse parse", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplaceAll(x, StringVal("a"), StringVal("aa")),
			Right: StringVal("aa"),
		}
		checked := Check(Assert(69, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
		if valid, found := BoolValue(result.Value, formula); !found || !valid {
			t.Fatalf("formula=(%v,%v)", valid, found)
		}
	})

	t.Run("multiple replacements", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplaceAll(x, StringVal("a"), StringVal("za")),
			Right: StringVal("zaza"),
		}
		checked := Check(Assert(70, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "aa" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("empty source is identity", func(t *testing.T) {
		formula := Equal{
			Left:  StringReplaceAll(x, StringVal(""), StringVal("!")),
			Right: StringVal("ab"),
		}
		checked := Check(Assert(71, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "ab" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("predicate selects inverse", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{
				Left:  StringReplaceAll(x, StringVal("a"), StringVal("z")),
				Right: StringVal("zz"),
			},
			StringContains(x, StringVal("a")),
			Equal{Left: StringLength(x), Right: Integer{Value: 2}},
		}}
		checked := Check(Assert(72, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "aa" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("incompatible targets", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{
				Left:  StringReplaceAll(x, StringVal("a"), StringVal("z")),
				Right: StringVal("zz"),
			},
			Equal{
				Left:  StringReplaceAll(x, StringVal("a"), StringVal("z")),
				Right: StringVal("q"),
			},
		}}
		checked := Check(Assert(73, New(), formula))
		if _, ok := checked.(Unsatisfiable); !ok {
			t.Fatalf("result=%T", checked)
		}
	})
}

func TestGroundAssignedStringReplaceOperands(t *testing.T) {
	x := StringConst(1, "x")
	source := StringConst(2, "source")
	replacement := StringConst(3, "replacement")
	target := StringConst(4, "target")
	sourceAlias := StringConst(5, "source_alias")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: source, Right: sourceAlias},
		Equal{Left: sourceAlias, Right: StringVal("a")},
		Equal{Left: replacement, Right: StringVal("z")},
		Equal{Left: target, Right: StringVal("zz")},
		Equal{Left: StringReplaceAll(x, source, replacement), Right: target},
		StringContains(x, source),
		Equal{Left: StringLength(x), Right: Integer{Value: 2}},
	}}
	checked := Check(Assert(80, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	for symbol, want := range map[Term[StringSort]]string{
		x: "aa", source: "a", sourceAlias: "a", replacement: "z", target: "zz",
	} {
		if actual, found := StringModelValue(result.Value, symbol); !found || actual != want {
			t.Fatalf("value=(%q,%v), want %q", actual, found, want)
		}
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	firstOnly := And{Values: []Term[BoolSort]{
		Equal{Left: source, Right: StringVal("a")},
		Equal{Left: replacement, Right: StringVal("z")},
		Equal{Left: target, Right: StringVal("za")},
		Equal{Left: StringReplace(x, source, replacement), Right: target},
	}}
	checked = Check(Assert(81, New(), firstOnly))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("first result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "aa" {
		t.Fatalf("first x=(%q,%v)", actual, found)
	}

	conflicting := And{Values: []Term[BoolSort]{
		Equal{Left: source, Right: StringVal("a")},
		Equal{Left: source, Right: StringVal("b")},
		Equal{
			Left:  StringReplaceAll(x, source, StringVal("z")),
			Right: StringVal("z"),
		},
	}}
	checked = Check(Assert(82, New(), conflicting))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("conflicting result=%T", checked)
	}
}

func TestShortestStringDeletionPreimageExhaustive(t *testing.T) {
	sources := []string{"a", "b", "aa", "ab", "ba", "aba"}
	targets := []string{"", "a", "b", "aa", "ab", "ba", "aba", "bab"}
	for _, source := range sources {
		for _, target := range targets {
			candidate, found, complete := shortestStringDeletionPreimage(target, source)
			if !complete {
				t.Fatalf("unexpected resource limit for source=%q target=%q", source, target)
			}
			if found && strings.ReplaceAll(candidate, source, "") != target {
				t.Fatalf("invalid preimage %q for source=%q target=%q", candidate, source, target)
			}
			limit := (len([]rune(target)) + 1) * len([]rune(source))
			bruteFound := false
			var search func(string, int)
			search = func(prefix string, remaining int) {
				if bruteFound {
					return
				}
				if strings.ReplaceAll(prefix, source, "") == target {
					bruteFound = true
					return
				}
				if remaining == 0 {
					return
				}
				search(prefix+"a", remaining-1)
				search(prefix+"b", remaining-1)
			}
			search("", limit)
			if found != bruteFound {
				t.Fatalf(
					"source=%q target=%q found=%v brute=%v candidate=%q",
					source, target, found, bruteFound, candidate,
				)
			}
		}
	}
	candidate, found, complete := shortestStringDeletionPreimage("🙂a", "🙂a")
	if !complete || !found || strings.ReplaceAll(candidate, "🙂a", "") != "🙂a" {
		t.Fatalf("unicode candidate=(%q,%v,%v)", candidate, found, complete)
	}
}

func TestCompactStringReplaceAllStreamingEquality(t *testing.T) {
	values := []string{"", "a", "b", "aa", "ab", "aba", "🙂", "a🙂a"}
	for _, candidate := range values {
		for _, source := range values {
			for _, replacement := range values {
				target := candidate
				if source != "" {
					target = strings.ReplaceAll(candidate, source, replacement)
				}
				equality := CompactStringReplaceEquality{
					Source: source, Replacement: replacement, Target: target, All: true,
				}
				if !compactStringReplacementEquals(candidate, equality) {
					t.Fatalf("rejected %q replace-all %q -> %q = %q", candidate, source, replacement, target)
				}
				equality.Target = target + "#"
				if compactStringReplacementEquals(candidate, equality) {
					t.Fatalf("accepted incorrect target for %q replace-all %q -> %q", candidate, source, replacement)
				}
			}
		}
	}
}

func TestGroundStringReplaceIndexedInteraction(t *testing.T) {
	x := StringConst(1, "x")
	t.Run("at selects replacement preimage", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{
				Left:  StringReplace(x, StringVal("a"), StringVal("z")),
				Right: StringVal("z"),
			},
			Equal{Left: StringAt(x, Integer{Value: 0}), Right: StringVal("a")},
		}}
		checked := Check(Assert(63, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("substring rejects every preimage", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			Equal{
				Left:  StringReplace(x, StringVal("a"), StringVal("z")),
				Right: StringVal("z"),
			},
			Equal{
				Left:  StringSubstring(x, Integer{Value: 0}, Integer{Value: 1}),
				Right: StringVal("b"),
			},
		}}
		checked := Check(Assert(64, New(), formula))
		if _, ok := checked.(Unsatisfiable); !ok {
			t.Fatalf("result=%T", checked)
		}
	})
}

func TestGroundStringReplacePredicateInteraction(t *testing.T) {
	x := StringConst(1, "x")
	replacement := Equal{
		Left:  StringReplace(x, StringVal("a"), StringVal("z")),
		Right: StringVal("z"),
	}
	t.Run("contains selects replacement preimage", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			replacement,
			StringContains(x, StringVal("a")),
			Equal{Left: StringLength(x), Right: Integer{Value: 1}},
		}}
		checked := Check(Assert(65, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("negated contains selects unchanged preimage", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			replacement,
			Not{Value: StringContains(x, StringVal("a"))},
		}}
		checked := Check(Assert(66, New(), formula))
		result, ok := checked.(Satisfiable)
		if !ok {
			t.Fatalf("result=%T", checked)
		}
		if actual, found := StringModelValue(result.Value, x); !found || actual != "z" {
			t.Fatalf("x=(%q,%v)", actual, found)
		}
	})

	t.Run("Boolean predicate rejects every preimage", func(t *testing.T) {
		formula := And{Values: []Term[BoolSort]{
			replacement,
			Or{Values: []Term[BoolSort]{
				StringHasPrefix(x, StringVal("b")),
				StringHasSuffix(x, StringVal("b")),
			}},
		}}
		checked := Check(Assert(67, New(), formula))
		if _, ok := checked.(Unsatisfiable); !ok {
			t.Fatalf("result=%T", checked)
		}
	})

	t.Run("foreign symbol remains unknown", func(t *testing.T) {
		y := StringConst(2, "y")
		formula := And{Values: []Term[BoolSort]{
			replacement,
			StringContains(y, StringVal("a")),
		}}
		checked := Check(Assert(68, New(), formula))
		if _, ok := checked.(Unknown); !ok {
			t.Fatalf("result=%T", checked)
		}
	})
}

func TestMultipleWordEquationInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	z := StringConst(3, "z")
	first := Equal{Left: StringConcat(x, y), Right: StringVal("abc")}
	second := Equal{
		Left:  StringConcat(x, StringVal("-"), z),
		Right: StringVal("a-tail"),
	}
	formula := And{Values: []Term[BoolSort]{first, second}}
	checked := Check(Assert(34, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "bc" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, z); !found || actual != "tail" {
		t.Fatalf("z=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	unicode := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("🙂a")},
		Equal{Left: StringConcat(x, StringVal("-"), z), Right: StringVal("🙂-tail")},
	}}
	checked = Check(Assert(35, New(), unicode))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("unicode result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "🙂" {
		t.Fatalf("unicode x=(%q,%v)", actual, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		first,
		Equal{Left: StringConcat(x, x), Right: StringVal("zz")},
	}}
	checked = Check(Assert(36, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestEightWordEquationInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	z := StringConst(3, "z")
	w := StringConst(4, "w")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abc")},
		Equal{Left: StringConcat(x, StringVal("-"), z), Right: StringVal("a-tail")},
		Equal{Left: StringConcat(y, w), Right: StringVal("bc!")},
		Equal{Left: StringConcat(z, w), Right: StringVal("tail!")},
		Equal{Left: StringConcat(StringVal("<"), x, y), Right: StringVal("<abc")},
		Equal{Left: StringConcat(x, y, StringVal(">")), Right: StringVal("abc>")},
		Equal{Left: StringConcat(StringVal("["), z, w), Right: StringVal("[tail!")},
		Equal{Left: StringConcat(z, w, StringVal("]")), Right: StringVal("tail!]")},
	}}
	checked := Check(Assert(37, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	for _, item := range []struct {
		expression Term[StringSort]
		expected   string
	}{
		{x, "a"},
		{y, "bc"},
		{z, "tail"},
		{w, "!"},
	} {
		if actual, found := StringModelValue(result.Value, item.expression); !found || actual != item.expected {
			t.Fatalf("value=(%q,%v), want=%q", actual, found, item.expected)
		}
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	impossible := And{Values: append(
		append([]Term[BoolSort]{}, formula.Values[:7]...),
		Equal{Left: StringConcat(z, w, StringVal("]")), Right: StringVal("wrong]")},
	)}
	checked = Check(Assert(38, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestOverflowWordEquationInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	z := StringConst(3, "z")
	w := StringConst(4, "w")
	formula := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("abc")},
		Equal{Left: StringConcat(x, StringVal("-"), z), Right: StringVal("a-tail")},
		Equal{Left: StringConcat(y, w), Right: StringVal("bc!")},
		Equal{Left: StringConcat(z, w), Right: StringVal("tail!")},
		Equal{Left: StringConcat(StringVal("<"), x, y), Right: StringVal("<abc")},
		Equal{Left: StringConcat(x, y, StringVal(">")), Right: StringVal("abc>")},
		Equal{Left: StringConcat(StringVal("["), z, w), Right: StringVal("[tail!")},
		Equal{Left: StringConcat(z, w, StringVal("]")), Right: StringVal("tail!]")},
		Equal{Left: StringConcat(StringVal("<"), x, StringVal("-"), z), Right: StringVal("<a-tail")},
		Equal{Left: StringConcat(x, StringVal("-"), z, StringVal(">")), Right: StringVal("a-tail>")},
		Equal{Left: StringConcat(StringVal("("), y, w), Right: StringVal("(bc!")},
		Equal{Left: StringConcat(z, w, StringVal(")")), Right: StringVal("tail!)")},
		Bool{Value: true},
		Bool{Value: true},
		Bool{Value: true},
		Bool{Value: true},
		Bool{Value: true},
	}}
	checked := Check(Assert(39, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	for _, item := range []struct {
		expression Term[StringSort]
		expected   string
	}{
		{x, "a"},
		{y, "bc"},
		{z, "tail"},
		{w, "!"},
	} {
		if actual, found := StringModelValue(result.Value, item.expression); !found || actual != item.expected {
			t.Fatalf("value=(%q,%v), want=%q", actual, found, item.expected)
		}
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
}

func TestOverflowWordEquationConstraintInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	z := StringConst(3, "z")
	w := StringConst(4, "w")
	v := StringConst(5, "v")
	a := StringToRegex(StringVal("a"))
	notA := StringToRegex(StringVal("z"))
	formula := And{Values: []Term[BoolSort]{
		Equal{
			Left:  StringConcat(x, StringVal("-"), y, StringVal("-"), z, StringVal("-"), w),
			Right: StringVal("a-b-c-d"),
		},
		Equal{Left: StringConcat(v, StringVal("!")), Right: StringVal("e!")},
		Equal{Left: StringLength(x), Right: Integer{Value: 1}},
		Equal{Left: StringLength(y), Right: Integer{Value: 1}},
		Equal{Left: StringLength(z), Right: Integer{Value: 1}},
		Equal{Left: StringLength(w), Right: Integer{Value: 1}},
		Equal{Left: StringLength(v), Right: Integer{Value: 1}},
		StringInRegex(x, a),
		StringInRegex(x, UnionRegex(a, notA)),
		StringInRegex(x, IntersectRegex(FullRegex[StringSort](), a)),
		StringInRegex(x, DifferenceRegex(a, notA)),
		StringInRegex(x, ComplementRegex(notA)),
		StringContains(x, StringVal("a")),
		StringHasPrefix(x, StringVal("a")),
		StringHasSuffix(x, StringVal("a")),
		Not{Value: Equal{Left: x, Right: StringVal("z")}},
		Not{Value: Equal{Left: x, Right: StringVal("")}},
	}}
	checked := Check(Assert(40, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	for _, item := range []struct {
		expression Term[StringSort]
		expected   string
	}{
		{x, "a"},
		{y, "b"},
		{z, "c"},
		{w, "d"},
		{v, "e"},
	} {
		if actual, found := StringModelValue(result.Value, item.expression); !found || actual != item.expected {
			t.Fatalf("value=(%q,%v), want=%q", actual, found, item.expected)
		}
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
}

func TestWordEquationRegexInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	equation := Equal{Left: StringConcat(x, y), Right: StringVal("abc")}
	language := UnionRegex(
		StringToRegex(StringVal("a")),
		StringToRegex(StringVal("ab")),
	)
	formula := And{Values: []Term[BoolSort]{
		equation,
		StringInRegex(x, language),
	}}
	checked := Check(Assert(37, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "bc" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	negative := And{Values: []Term[BoolSort]{
		equation,
		Not{Value: StringInRegex(x, StringToRegex(StringVal("")))},
	}}
	checked = Check(Assert(38, New(), negative))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("negative result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
		t.Fatalf("negative x=(%q,%v)", actual, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		equation,
		StringInRegex(x, StringToRegex(StringVal("z"))),
	}}
	checked = Check(Assert(39, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestWordEquationBooleanRegexInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	equation := Equal{Left: StringConcat(x, y), Right: StringVal("abc")}
	choice := Or{Values: []Term[BoolSort]{
		StringInRegex(x, StringToRegex(StringVal("z"))),
		StringInRegex(x, StringToRegex(StringVal("a"))),
	}}
	formula := And{Values: []Term[BoolSort]{equation, choice}}
	checked := Check(Assert(40, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "bc" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	unicode := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("🙂a")},
		Or{Values: []Term[BoolSort]{
			StringInRegex(x, StringToRegex(StringVal("z"))),
			StringInRegex(x, StringToRegex(StringVal("🙂"))),
		}},
	}}
	checked = Check(Assert(41, New(), unicode))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("unicode result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "🙂" {
		t.Fatalf("unicode x=(%q,%v)", actual, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		equation,
		Or{Values: []Term[BoolSort]{
			StringInRegex(x, StringToRegex(StringVal("z"))),
			StringInRegex(x, StringToRegex(StringVal("q"))),
		}},
	}}
	checked = Check(Assert(42, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestWordEquationStringDisequalityInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	equation := Equal{Left: StringConcat(x, y), Right: StringVal("ab")}
	nonempty := Not{Value: Equal{Left: x, Right: StringVal("")}}
	formula := And{Values: []Term[BoolSort]{equation, nonempty}}
	checked := Check(Assert(43, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "b" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	choice := And{Values: []Term[BoolSort]{
		equation,
		Or{Values: []Term[BoolSort]{
			Equal{Left: x, Right: StringVal("z")},
			Equal{Left: x, Right: StringVal("a")},
		}},
	}}
	checked = Check(Assert(44, New(), choice))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("choice result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "a" {
		t.Fatalf("choice x=(%q,%v)", actual, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("")},
		nonempty,
	}}
	checked = Check(Assert(45, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestWordEquationStringPredicateInteraction(t *testing.T) {
	x := StringConst(1, "x")
	y := StringConst(2, "y")
	equation := Equal{Left: StringConcat(x, y), Right: StringVal("abc")}
	formula := And{Values: []Term[BoolSort]{
		equation,
		StringContains(x, StringVal("b")),
		StringHasPrefix(x, StringVal("a")),
	}}
	checked := Check(Assert(46, New(), formula))
	result, ok := checked.(Satisfiable)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "ab" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := StringModelValue(result.Value, y); !found || actual != "c" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := BoolValue(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	unicode := And{Values: []Term[BoolSort]{
		Equal{Left: StringConcat(x, y), Right: StringVal("🙂a")},
		StringContains(x, StringVal("🙂")),
	}}
	checked = Check(Assert(47, New(), unicode))
	result, ok = checked.(Satisfiable)
	if !ok {
		t.Fatalf("unicode result=%T", checked)
	}
	if actual, found := StringModelValue(result.Value, x); !found || actual != "🙂" {
		t.Fatalf("unicode x=(%q,%v)", actual, found)
	}

	impossible := And{Values: []Term[BoolSort]{
		equation,
		StringContains(x, StringVal("z")),
	}}
	checked = Check(Assert(48, New(), impossible))
	if _, ok := checked.(Unsatisfiable); !ok {
		t.Fatalf("impossible result=%T", checked)
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
