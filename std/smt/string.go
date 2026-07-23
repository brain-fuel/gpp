package smt

import (
	"strings"
	"unicode/utf8"
)

const (
	compactStringLiteral = iota
	compactStringSymbol
	compactStringSingleSymbolConcat
)

const (
	CompactStringEqual = iota
	CompactStringLengthEqual
	CompactStringLengthLess
	CompactStringLengthLessEqual
	CompactStringContains
	CompactStringPrefix
	CompactStringSuffix
)

type CompactStringTerm struct {
	Kind   uint8
	ID     int
	Name   string
	Value  string
	Suffix string
}

type CompactStringRelation struct {
	Kind    uint8
	Negated bool
	Left    CompactStringTerm
	Right   CompactStringTerm
	Integer int64
}

// CompactStringLengthRelation compares the code-point lengths of two compact
// string expressions. Order is 0 for equality, 1 for strict less-than, and 2
// for less-than-or-equal.
type CompactStringLengthRelation struct {
	Left  CompactStringTerm
	Right CompactStringTerm
	Order uint8
}

func (CompactStringLengthRelation) isTerm(BoolSort) {}

type CompactStringSystem struct {
	Count    int
	Inline   [8]CompactStringRelation
	Overflow []CompactStringRelation
}

func CompactStringLiteralTerm(value string) CompactStringTerm {
	return CompactStringTerm{Kind: compactStringLiteral, Value: value}
}

func CompactStringSymbolTerm(id int, name string) CompactStringTerm {
	return CompactStringTerm{Kind: compactStringSymbol, ID: id, Name: name}
}

func CompactStringSingleSymbolConcatTerm(prefix string, id int, name, suffix string) CompactStringTerm {
	return CompactStringTerm{
		Kind: compactStringSingleSymbolConcat, ID: id, Name: name,
		Value: prefix, Suffix: suffix,
	}
}

func MaterializeCompactStringTerm(term CompactStringTerm) Term[StringSort] {
	switch term.Kind {
	case compactStringLiteral:
		return StringVal(term.Value)
	case compactStringSymbol:
		return StringConst(term.ID, term.Name)
	case compactStringSingleSymbolConcat:
		return StringConcat(
			StringVal(term.Value),
			StringConst(term.ID, term.Name),
			StringVal(term.Suffix),
		)
	default:
		panic("smt: invalid compact string term")
	}
}

func AppendCompactStringRelation(system CompactStringSystem, relation CompactStringRelation) CompactStringSystem {
	if system.Count < len(system.Inline) && system.Overflow == nil {
		system.Inline[system.Count] = relation
		system.Count++
		return system
	}
	if system.Overflow == nil {
		system.Overflow = make([]CompactStringRelation, system.Count, system.Count*2)
		copy(system.Overflow, system.Inline[:system.Count])
	}
	system.Overflow = append(system.Overflow, relation)
	system.Count++
	return system
}

func CompactStringAssertions(system CompactStringSystem) Term[BoolSort] {
	return stringSystem{system: system}
}

func (system CompactStringSystem) relations() []CompactStringRelation {
	if system.Overflow != nil {
		return system.Overflow[:system.Count]
	}
	return system.Inline[:system.Count]
}

type stringModelEntry struct {
	id    int
	value string
}

type stringModel struct {
	count    int
	inline   [4]stringModelEntry
	overflow map[int]string
}

func makeStringConcat(values []Term[StringSort]) Term[StringSort] {
	switch len(values) {
	case 0:
		return stringValue[StringSort]{value: ""}
	case 1:
		return values[0]
	}
	total := 0
	for _, value := range values {
		literal, ok := value.(stringValue[StringSort])
		if !ok {
			return stringConcat[StringSort]{values: values}
		}
		total += len(literal.value)
	}
	var result strings.Builder
	result.Grow(total)
	for _, value := range values {
		result.WriteString(value.(stringValue[StringSort]).value)
	}
	return stringValue[StringSort]{value: result.String()}
}

// DecodeStringCodePoints decodes the SMT-LIB character domain, including
// surrogate code points represented with their three-byte WTF-8 encoding.
func DecodeStringCodePoints(value string) []rune {
	result := make([]rune, 0, len(value))
	for offset := 0; offset < len(value); {
		first := value[offset]
		if first < 0x80 {
			result = append(result, rune(first))
			offset++
			continue
		}
		width := 0
		var code rune
		switch {
		case first&0xe0 == 0xc0:
			width, code = 2, rune(first&0x1f)
		case first&0xf0 == 0xe0:
			width, code = 3, rune(first&0x0f)
		case first&0xf8 == 0xf0:
			width, code = 4, rune(first&0x07)
		default:
			result = append(result, utf8.RuneError)
			offset++
			continue
		}
		if offset+width > len(value) {
			result = append(result, utf8.RuneError)
			offset++
			continue
		}
		valid := true
		for index := 1; index < width; index++ {
			next := value[offset+index]
			if next&0xc0 != 0x80 {
				valid = false
				break
			}
			code = code<<6 | rune(next&0x3f)
		}
		if !valid {
			result = append(result, utf8.RuneError)
			offset++
			continue
		}
		result = append(result, code)
		offset += width
	}
	return result
}

func EncodeStringCodePoint(value int64) (string, bool) {
	if value < 0 || value > 0x2ffff {
		return "", false
	}
	code := rune(value)
	switch {
	case value < 0x80:
		return string([]byte{byte(value)}), true
	case value < 0x800:
		return string([]byte{0xc0 | byte(code>>6), 0x80 | byte(code&0x3f)}), true
	case value < 0x10000:
		return string([]byte{0xe0 | byte(code>>12), 0x80 | byte(code>>6&0x3f), 0x80 | byte(code&0x3f)}), true
	default:
		return string([]byte{0xf0 | byte(code>>18), 0x80 | byte(code>>12&0x3f), 0x80 | byte(code>>6&0x3f), 0x80 | byte(code&0x3f)}), true
	}
}

type stringSymbols struct {
	count    int
	inline   [8]int
	overflow map[int]struct{}
}

func (symbols *stringSymbols) add(id int) {
	if symbols.contains(id) {
		return
	}
	if symbols.count < len(symbols.inline) {
		symbols.inline[symbols.count] = id
		symbols.count++
		return
	}
	if symbols.overflow == nil {
		symbols.overflow = make(map[int]struct{})
	}
	symbols.overflow[id] = struct{}{}
}

func (symbols stringSymbols) contains(id int) bool {
	for index := 0; index < symbols.count; index++ {
		if symbols.inline[index] == id {
			return true
		}
	}
	_, ok := symbols.overflow[id]
	return ok
}

func (model *stringModel) set(id int, value string) {
	if model.count < len(model.inline) {
		model.inline[model.count] = stringModelEntry{id: id, value: value}
		model.count++
		return
	}
	if model.overflow == nil {
		model.overflow = make(map[int]string)
	}
	model.overflow[id] = value
}

func (model stringModel) lookup(id int) (string, bool) {
	for index := 0; index < model.count; index++ {
		if model.inline[index].id == id {
			return model.inline[index].value, true
		}
	}
	value, ok := model.overflow[id]
	return value, ok
}

func evaluateString(term Term[StringSort], model stringModel, integers integerModel) (string, bool) {
	switch value := term.(type) {
	case stringValue[StringSort]:
		return value.value, true
	case stringSymbol[StringSort]:
		return model.lookup(value.iD)
	case stringConcat[StringSort]:
		var result strings.Builder
		for _, item := range value.values {
			part, ok := evaluateString(item, model, integers)
			if !ok {
				return "", false
			}
			result.WriteString(part)
		}
		return result.String(), true
	case stringAt[StringSort]:
		text, textOK := evaluateString(value.value, model, integers)
		index, indexOK := evaluateStringOffset(value.index, integers)
		if !textOK || !indexOK {
			return "", false
		}
		if index < 0 {
			return "", true
		}
		start, _, found := stringCodePointByteOffset(text, index)
		if !found || start == len(text) {
			return "", true
		}
		width := stringCodePointWidth(text, start)
		if width == 1 && text[start] >= 0x80 {
			return string(utf8.RuneError), true
		}
		return text[start : start+width], true
	case stringSubstring[StringSort]:
		text, textOK := evaluateString(value.value, model, integers)
		offset, offsetOK := evaluateStringOffset(value.offset, integers)
		length, lengthOK := evaluateStringOffset(value.length, integers)
		if !textOK || !offsetOK || !lengthOK {
			return "", false
		}
		if offset < 0 || length <= 0 {
			return "", true
		}
		start, _, found := stringCodePointByteOffset(text, offset)
		if !found || start == len(text) {
			return "", true
		}
		end := start
		valid := true
		for remaining := length; remaining > 0 && end < len(text); remaining-- {
			width := stringCodePointWidth(text, end)
			valid = valid && (width != 1 || text[end] < 0x80)
			end += width
		}
		if !valid {
			codes := DecodeStringCodePoints(text)
			last := offset + length
			if last < offset || last > int64(len(codes)) {
				last = int64(len(codes))
			}
			return string(codes[offset:last]), true
		}
		return text[start:end], true
	case stringReplace[StringSort]:
		text, textOK := evaluateString(value.value, model, integers)
		source, sourceOK := evaluateString(value.source, model, integers)
		replacement, replacementOK := evaluateString(value.replacement, model, integers)
		if !textOK || !sourceOK || !replacementOK {
			return "", false
		}
		return strings.Replace(text, source, replacement, 1), true
	case stringReplaceAll[StringSort]:
		text, textOK := evaluateString(value.value, model, integers)
		source, sourceOK := evaluateString(value.source, model, integers)
		replacement, replacementOK := evaluateString(value.replacement, model, integers)
		if !textOK || !sourceOK || !replacementOK {
			return "", false
		}
		if source == "" {
			return text, true
		}
		return strings.ReplaceAll(text, source, replacement), true
	case integerToString[StringSort]:
		integer, ok := evaluateInteger(value.value, booleanModel{}, integers, rationalModel{})
		if !ok {
			return "", false
		}
		if CompareIntegerValue(integer, NewIntegerValue(0)) < 0 {
			return "", true
		}
		return integer.String(), true
	case codeToString[StringSort]:
		integer, ok := evaluateInteger(value.value, booleanModel{}, integers, rationalModel{})
		if !ok {
			return "", false
		}
		small, fits := integer.Int64()
		if !fits {
			return "", true
		}
		encoded, valid := EncodeStringCodePoint(small)
		if !valid {
			return "", true
		}
		return encoded, true
	default:
		return "", false
	}
}

func evaluateBoolWithStringsAndDatatypes(term Term[BoolSort], booleans booleanModel, integers integerModel, reals rationalModel, strings stringModel, datatypes *datatypeModel) (bool, bool) {
	if containsStringTheory(term) {
		return evaluateStringBoolean(term, strings, integers)
	}
	return evaluateBoolWithDatatypes(term, booleans, integers, reals, datatypes)
}

func containsStringTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case stringContains, stringPrefix, stringSuffix, stringIsDigit, stringInRegex, stringSystem,
		CompactStringBooleanFormula, CompactStringWordEquation, CompactStringLengthRelation,
		CompactStringIndexedEquality, CompactStringReplaceEquality, *CompactGroundIndexedStringFormula,
		CompactStringIndexOfEquality, *CompactGroundStringEvaluationFormula:
		return true
	case Equal:
		return isStringTerm(value.Left) || isStringTerm(value.Right) || isStringIntegerTerm(value.Left) || isStringIntegerTerm(value.Right)
	case Not:
		return containsStringTheory(value.Value)
	case And:
		for _, item := range value.Values {
			if containsStringTheory(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsStringTheory(item) {
				return true
			}
		}
	case Or:
		for _, item := range value.Values {
			if containsStringTheory(item) {
				return true
			}
		}
	case Implies:
		return containsStringTheory(value.Left) || containsStringTheory(value.Right)
	case Iff:
		return containsStringTheory(value.Left) || containsStringTheory(value.Right)
	case If[BoolSort]:
		return containsStringTheory(value.Condition) || containsStringTheory(value.Then) || containsStringTheory(value.Else)
	}
	return false
}

func isStringTerm(term any) bool {
	switch term.(type) {
	case stringValue[StringSort], stringSymbol[StringSort], stringConcat[StringSort], stringAt[StringSort], stringSubstring[StringSort], stringReplace[StringSort], stringReplaceAll[StringSort], integerToString[StringSort], codeToString[StringSort]:
		return true
	default:
		return false
	}
}

func isStringIntegerTerm(term any) bool {
	switch term.(type) {
	case stringLength, stringIndexOf, stringToInteger, stringToCode:
		return true
	default:
		return false
	}
}

func solveStringAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if outcome, recognized := solveGroundStringReplaceEqualities(assertions); recognized {
		return outcome, true
	}
	if outcome, recognized := solveGroundIndexedStringEqualities(assertions); recognized {
		return outcome, true
	}
	if outcome, recognized := solveGroundAssignedStringEvaluation(assertions); recognized {
		return outcome, true
	}
	if outcome, recognized := solveBoundedWordEquationConjunction(assertions); recognized {
		return outcome, true
	}
	if outcome, recognized := solveBoundedGroundWordEquationAssertion(assertions); recognized {
		return outcome, true
	}
	if outcome, recognized := solveCompactStringWordEquationAssertions(assertions); recognized {
		return outcome, true
	}
	if outcome, recognized := solveCompactStringBooleanAssertions(assertions); recognized {
		return outcome, true
	}
	if containsBooleanStringAssertions(assertions) {
		return solveBooleanStringAssertions(assertions)
	}
	var forcedModel stringModel
	var symbols stringSymbols
	for _, assertion := range assertions {
		if value, ground := evaluateStringBoolean(assertion, stringModel{}, integerModel{}); ground && !value {
			return checkOutcome{status: checkUnsat}, true
		}
		collectStringSymbolsBoolean(assertion, &symbols)
	}
	for pass := 0; pass < len(assertions)+1; pass++ {
		changed := false
		for _, assertion := range assertions {
			changed = bindForcedStringAssertion(assertion, false, &forcedModel) || changed
		}
		if !changed {
			break
		}
	}
	forcedComplete := allStringSymbolsBound(symbols, forcedModel)
	model := forcedModel
	for pass := 0; pass < len(assertions)+1; pass++ {
		changed := false
		for _, assertion := range assertions {
			changed = bindStringAssertion(assertion, false, &model) || changed
		}
		if !changed {
			break
		}
	}
	regexConstraints := make([]symbolicRegexConstraint, 0, 8)
	for _, assertion := range assertions {
		collectSymbolicRegexConstraints(assertion, false, &regexConstraints)
	}
	if combinedStringRegexConstraintsImpossible(regexConstraints, model) {
		return checkOutcome{status: checkUnsat}, true
	}
	synthesizeCombinedStringRegexConstraints(regexConstraints, &model)
	for _, assertion := range assertions {
		synthesizeStringAssertion(assertion, false, &model)
	}
	defaultUnboundStrings(symbols, &model)
	for _, assertion := range assertions {
		value, ok := evaluateStringBoolean(assertion, model, integerModel{})
		if !ok {
			return checkOutcome{}, false
		}
		if !value {
			// A failed synthesized candidate is not, by itself, an
			// unsatisfiability proof. Ground formulas are complete; symbolic
			// formulas outside the constructive fragment must remain unknown.
			if symbols.count == 0 && len(symbols.overflow) == 0 || forcedComplete {
				return checkOutcome{status: checkUnsat}, true
			}
			return checkOutcome{}, false
		}
	}
	return checkOutcome{status: checkSat, strings: model}, true
}

func solveGroundAssignedStringEvaluation(
	assertions []Term[BoolSort],
) (checkOutcome, bool) {
	if len(assertions) == 1 {
		if compact, ok := assertions[0].(*CompactGroundStringEvaluationFormula); ok {
			return solveCompactGroundStringEvaluation(compact), true
		}
	}
	var storage boundedWordEquationConjuncts
	for _, assertion := range assertions {
		appendBoundedWordEquationConjunct(assertion, &storage)
	}
	conjuncts := storage.values()
	if len(conjuncts) == 0 {
		return checkOutcome{}, false
	}
	strings, stringConflict := groundStringReplaceAssignments(conjuncts)
	integers, integerConflict := groundIndexedIntegerAssignments(conjuncts)
	if stringConflict || integerConflict {
		return checkOutcome{status: checkUnsat}, true
	}
	for _, conjunct := range conjuncts {
		value, known := evaluateStringBoolean(conjunct, strings, integers)
		if !known {
			return checkOutcome{}, false
		}
		if !value {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	return checkOutcome{
		status: checkSat, strings: strings, integers: integers,
	}, true
}

func solveCompactGroundStringEvaluation(
	formula *CompactGroundStringEvaluationFormula,
) checkOutcome {
	var strings stringModel
	for pass := 0; pass < int(formula.StringAssignmentCount)+1; pass++ {
		changed := false
		for index := 0; index < int(formula.StringAssignmentCount); index++ {
			relation := formula.StringAssignments[index]
			left, leftOK := evaluateCompactString(relation.Left, strings)
			right, rightOK := evaluateCompactString(relation.Right, strings)
			if relation.Left.Kind == compactStringSymbol && rightOK {
				if existing, found := strings.lookup(relation.Left.ID); found && existing != right {
					return checkOutcome{status: checkUnsat}
				}
				changed = setExistingString(&strings, relation.Left.ID, right) || changed
			}
			if relation.Right.Kind == compactStringSymbol && leftOK {
				if existing, found := strings.lookup(relation.Right.ID); found && existing != left {
					return checkOutcome{status: checkUnsat}
				}
				changed = setExistingString(&strings, relation.Right.ID, left) || changed
			}
		}
		if !changed {
			break
		}
	}
	var integers integerModel
	for index := 0; index < int(formula.IntegerAssignmentCount); index++ {
		assignment := formula.IntegerAssignments[index]
		outcome := solveCompactIntegerLinearEquality(assignment)
		if outcome.status != checkSat {
			return outcome
		}
		value, found := outcome.integers.lookup(assignment.ID)
		if !found {
			continue
		}
		if existing, assigned := integers.lookup(assignment.ID); assigned {
			if CompareIntegerValue(existing, value) != 0 {
				return checkOutcome{status: checkUnsat}
			}
			continue
		}
		integers.set(assignment.ID, value)
	}
	for index := 0; index < int(formula.IndexOfCount); index++ {
		valid, known := evaluateCompactStringIndexOfEquality(
			formula.IndexOf[index], strings, integers,
		)
		if !known {
			return checkOutcome{}
		}
		if !valid {
			return checkOutcome{status: checkUnsat}
		}
	}
	return checkOutcome{
		status: checkSat, strings: strings, integers: integers,
	}
}

func evaluateCompactStringIndexOfEquality(
	equality CompactStringIndexOfEquality,
	strings stringModel,
	integers integerModel,
) (bool, bool) {
	text, textOK := strings.lookup(equality.TextID)
	needle, needleOK := strings.lookup(equality.NeedleID)
	offset, offsetOK := integers.lookup(equality.OffsetID)
	result, resultOK := integers.lookup(equality.ResultID)
	offsetValue, offsetFits := offset.Int64()
	resultValue, resultFits := result.Int64()
	if !textOK || !needleOK || !offsetOK || !resultOK || !offsetFits || !resultFits {
		return false, false
	}
	return stringIndexOfRunes(text, needle, offsetValue) == resultValue, true
}

func allStringSymbolsBound(symbols stringSymbols, model stringModel) bool {
	for index := 0; index < symbols.count; index++ {
		if _, ok := model.lookup(symbols.inline[index]); !ok {
			return false
		}
	}
	for id := range symbols.overflow {
		if _, ok := model.lookup(id); !ok {
			return false
		}
	}
	return true
}

func solveCompactStringSystem(system CompactStringSystem) (checkOutcome, bool) {
	var model stringModel
	var symbols stringSymbols
	relations := system.relations()
	for _, relation := range relations {
		if relation.Left.Kind == compactStringLiteral &&
			(relation.Kind >= CompactStringLengthEqual && relation.Kind <= CompactStringLengthLessEqual ||
				relation.Right.Kind == compactStringLiteral) {
			if value, complete := evaluateCompactStringRelation(relation, stringModel{}); complete && !value {
				return checkOutcome{status: checkUnsat}, true
			}
		}
		if relation.Kind == CompactStringLengthEqual && !relation.Negated && relation.Integer < 0 {
			return checkOutcome{status: checkUnsat}, true
		}
		if relation.Kind == CompactStringLengthLess && !relation.Negated && relation.Integer <= 0 ||
			relation.Kind == CompactStringLengthLessEqual && !relation.Negated && relation.Integer < 0 {
			return checkOutcome{status: checkUnsat}, true
		}
		if relation.Left.Kind == compactStringSymbol || relation.Left.Kind == compactStringSingleSymbolConcat {
			symbols.add(relation.Left.ID)
		}
		if relation.Right.Kind == compactStringSymbol || relation.Right.Kind == compactStringSingleSymbolConcat {
			symbols.add(relation.Right.ID)
		}
	}
	for pass := 0; pass < len(relations)+1; pass++ {
		changed := false
		for _, relation := range relations {
			if relation.Kind != CompactStringEqual || relation.Negated {
				continue
			}
			if relation.Left.Kind == compactStringSingleSymbolConcat {
				if right, ok := evaluateCompactString(relation.Right, model); ok {
					value, possible := solveCompactSingleSymbolConcat(relation.Left, right)
					if !possible {
						return checkOutcome{status: checkUnsat}, true
					}
					if existing, bound := model.lookup(relation.Left.ID); bound && existing != value {
						return checkOutcome{status: checkUnsat}, true
					}
					changed = setExistingString(&model, relation.Left.ID, value) || changed
					continue
				}
			}
			if relation.Right.Kind == compactStringSingleSymbolConcat {
				if left, ok := evaluateCompactString(relation.Left, model); ok {
					value, possible := solveCompactSingleSymbolConcat(relation.Right, left)
					if !possible {
						return checkOutcome{status: checkUnsat}, true
					}
					if existing, bound := model.lookup(relation.Right.ID); bound && existing != value {
						return checkOutcome{status: checkUnsat}, true
					}
					changed = setExistingString(&model, relation.Right.ID, value) || changed
					continue
				}
			}
			left, leftOK := evaluateCompactString(relation.Left, model)
			right, rightOK := evaluateCompactString(relation.Right, model)
			if relation.Left.Kind == compactStringSymbol && rightOK {
				if existing, bound := model.lookup(relation.Left.ID); bound && existing != right {
					return checkOutcome{status: checkUnsat}, true
				}
				changed = setExistingString(&model, relation.Left.ID, right) || changed
			}
			if relation.Right.Kind == compactStringSymbol && leftOK {
				if existing, bound := model.lookup(relation.Right.ID); bound && existing != left {
					return checkOutcome{status: checkUnsat}, true
				}
				changed = setExistingString(&model, relation.Right.ID, left) || changed
			}
		}
		if !changed {
			break
		}
	}
	for _, relation := range relations {
		if relation.Kind != CompactStringEqual || !relation.Negated {
			continue
		}
		if relation.Left.Kind == compactStringSymbol && relation.Right.Kind == compactStringSymbol && relation.Left.ID == relation.Right.ID {
			return checkOutcome{status: checkUnsat}, true
		}
		left, leftOK := evaluateCompactString(relation.Left, model)
		right, rightOK := evaluateCompactString(relation.Right, model)
		if leftOK && rightOK && left == right {
			return checkOutcome{status: checkUnsat}, true
		}
		if relation.Left.Kind == compactStringSymbol && !leftOK && rightOK {
			setExistingString(&model, relation.Left.ID, right+"a")
		} else if relation.Right.Kind == compactStringSymbol && !rightOK && leftOK {
			setExistingString(&model, relation.Right.ID, left+"a")
		} else if relation.Left.Kind == compactStringSymbol && relation.Right.Kind == compactStringSymbol && !leftOK && !rightOK {
			setExistingString(&model, relation.Left.ID, "")
			setExistingString(&model, relation.Right.ID, "a")
		}
	}
	for _, relation := range relations {
		if relation.Kind < CompactStringContains || relation.Left.Kind != compactStringSymbol {
			continue
		}
		if _, bound := model.lookup(relation.Left.ID); bound {
			continue
		}
		part, ok := evaluateCompactString(relation.Right, model)
		if !ok {
			continue
		}
		candidate := part
		if relation.Negated && part != "" {
			candidate = ""
		}
		setExistingString(&model, relation.Left.ID, candidate)
	}
	var lengthConstraints boundedWordEquationConstraints
	for _, relation := range relations {
		if relation.Left.Kind != compactStringSymbol {
			continue
		}
		var recognized, contradiction bool
		switch relation.Kind {
		case CompactStringLengthEqual:
			if relation.Negated {
				continue
			}
			recognized, contradiction = assignBoundedWordEquationLength(
				&lengthConstraints, relation.Left.ID, relation.Integer,
			)
		case CompactStringLengthLess, CompactStringLengthLessEqual:
			minimum, maximum, hasMaximum := compactStringLengthRange(relation)
			recognized, contradiction = assignBoundedWordEquationLengthRange(
				&lengthConstraints, relation.Left.ID, minimum, maximum, hasMaximum,
			)
		default:
			continue
		}
		if !recognized {
			return checkOutcome{}, false
		}
		if contradiction {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	for index := 0; index < lengthConstraints.lengthCount; index++ {
		constraint := lengthConstraints.lengths[index]
		if existing, bound := model.lookup(constraint.id); bound {
			if !constraint.allows(int64(stringCodePointCount(existing))) {
				return checkOutcome{status: checkUnsat}, true
			}
			continue
		}
		if constraint.minimum > int64(^uint(0)>>1) {
			return checkOutcome{}, false
		}
		setExistingString(&model, constraint.id, strings.Repeat("a", int(constraint.minimum)))
	}
	defaultUnboundStrings(symbols, &model)
	for _, relation := range relations {
		value, complete := evaluateCompactStringRelation(relation, model)
		if !complete {
			return checkOutcome{}, false
		}
		if !value {
			return checkOutcome{}, false
		}
	}
	return checkOutcome{status: checkSat, strings: model}, true
}

func evaluateCompactString(term CompactStringTerm, model stringModel) (string, bool) {
	if term.Kind == compactStringLiteral {
		return term.Value, true
	}
	if term.Kind == compactStringSymbol {
		return model.lookup(term.ID)
	}
	if term.Kind == compactStringSingleSymbolConcat {
		value, ok := model.lookup(term.ID)
		if !ok {
			return "", false
		}
		return term.Value + value + term.Suffix, true
	}
	return "", false
}

func solveCompactSingleSymbolConcat(term CompactStringTerm, target string) (string, bool) {
	if len(target) < len(term.Value)+len(term.Suffix) ||
		!strings.HasPrefix(target, term.Value) || !strings.HasSuffix(target, term.Suffix) {
		return "", false
	}
	return target[len(term.Value) : len(target)-len(term.Suffix)], true
}

func CompactStringModelValue(model Model, term CompactStringTerm) (string, bool) {
	return evaluateCompactString(term, model.strings)
}

func CompactStringRelationValue(model Model, relation CompactStringRelation) (bool, bool) {
	return evaluateCompactStringRelation(relation, model.strings)
}

func evaluateCompactStringRelation(relation CompactStringRelation, model stringModel) (bool, bool) {
	result, complete := false, false
	switch relation.Kind {
	case CompactStringEqual:
		result, complete = evaluateCompactStringEquality(relation.Left, relation.Right, model)
	case CompactStringLengthEqual:
		left, leftOK := evaluateCompactString(relation.Left, model)
		result = int64(stringCodePointCount(left)) == relation.Integer
		complete = leftOK
	case CompactStringLengthLess:
		left, leftOK := evaluateCompactString(relation.Left, model)
		result = int64(stringCodePointCount(left)) < relation.Integer
		complete = leftOK
	case CompactStringLengthLessEqual:
		left, leftOK := evaluateCompactString(relation.Left, model)
		result = int64(stringCodePointCount(left)) <= relation.Integer
		complete = leftOK
	case CompactStringContains:
		left, leftOK := evaluateCompactString(relation.Left, model)
		right, rightOK := evaluateCompactString(relation.Right, model)
		result, complete = strings.Contains(left, right), leftOK && rightOK
	case CompactStringPrefix:
		left, leftOK := evaluateCompactString(relation.Left, model)
		right, rightOK := evaluateCompactString(relation.Right, model)
		result, complete = strings.HasPrefix(left, right), leftOK && rightOK
	case CompactStringSuffix:
		left, leftOK := evaluateCompactString(relation.Left, model)
		right, rightOK := evaluateCompactString(relation.Right, model)
		result, complete = strings.HasSuffix(left, right), leftOK && rightOK
	default:
		return false, false
	}
	if relation.Negated {
		result = !result
	}
	return result, complete
}

func evaluateCompactStringEquality(left, right CompactStringTerm, model stringModel) (bool, bool) {
	if left.Kind == compactStringSingleSymbolConcat {
		if target, ok := evaluateCompactString(right, model); ok {
			value, bound := model.lookup(left.ID)
			if !bound {
				return false, false
			}
			return compactSingleSymbolConcatMatches(left, value, target), true
		}
	}
	if right.Kind == compactStringSingleSymbolConcat {
		if target, ok := evaluateCompactString(left, model); ok {
			value, bound := model.lookup(right.ID)
			if !bound {
				return false, false
			}
			return compactSingleSymbolConcatMatches(right, value, target), true
		}
	}
	leftValue, leftOK := evaluateCompactString(left, model)
	rightValue, rightOK := evaluateCompactString(right, model)
	return leftValue == rightValue, leftOK && rightOK
}

func compactSingleSymbolConcatMatches(term CompactStringTerm, value, target string) bool {
	if len(target) != len(term.Value)+len(value)+len(term.Suffix) ||
		!strings.HasPrefix(target, term.Value) || !strings.HasSuffix(target, term.Suffix) {
		return false
	}
	return target[len(term.Value):len(target)-len(term.Suffix)] == value
}

func collectStringSymbolsBoolean(term Term[BoolSort], symbols *stringSymbols) {
	switch value := term.(type) {
	case CompactStringLengthRelation:
		if value.Left.Kind == compactStringSymbol || value.Left.Kind == compactStringSingleSymbolConcat {
			symbols.add(value.Left.ID)
		}
		if value.Right.Kind == compactStringSymbol || value.Right.Kind == compactStringSingleSymbolConcat {
			symbols.add(value.Right.ID)
		}
	case CompactStringWordEquation:
		for index := 0; index < value.Pattern.Count; index++ {
			symbols.add(value.Pattern.SymbolIDs[index])
		}
	case CompactStringIndexedEquality:
		symbols.add(value.SymbolID)
	case CompactStringReplaceEquality:
		symbols.add(value.SymbolID)
		if value.SourceSymbol {
			symbols.add(value.SourceID)
		}
		if value.ReplacementSymbol {
			symbols.add(value.ReplacementID)
		}
		if value.TargetSymbol {
			symbols.add(value.TargetID)
		}
	case CompactStringBooleanFormula:
		for index := 0; index < value.AtomCount; index++ {
			symbols.add(value.Atoms[index].SymbolID)
		}
	case stringSystem:
		for _, relation := range value.system.relations() {
			if relation.Left.Kind == compactStringSymbol || relation.Left.Kind == compactStringSingleSymbolConcat {
				symbols.add(relation.Left.ID)
			}
			if relation.Right.Kind == compactStringSymbol || relation.Right.Kind == compactStringSingleSymbolConcat {
				symbols.add(relation.Right.ID)
			}
		}
	case Equal:
		collectStringSymbols(value.Left, symbols)
		collectStringSymbols(value.Right, symbols)
	case stringContains:
		collectStringSymbols(value.value, symbols)
		collectStringSymbols(value.substring, symbols)
	case stringPrefix:
		collectStringSymbols(value.prefix, symbols)
		collectStringSymbols(value.value, symbols)
	case stringSuffix:
		collectStringSymbols(value.suffix, symbols)
		collectStringSymbols(value.value, symbols)
	case stringInRegex:
		collectStringSymbols(value.value, symbols)
		if value.expression.node != nil {
			collectRegexStringSymbols(value.expression.node, symbols)
		}
	case stringIsDigit:
		collectStringSymbols(value.value, symbols)
	case Not:
		collectStringSymbolsBoolean(value.Value, symbols)
	case And:
		for _, item := range value.Values {
			collectStringSymbolsBoolean(item, symbols)
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			collectStringSymbolsBoolean(item, symbols)
		}
	case Or:
		for _, item := range value.Values {
			collectStringSymbolsBoolean(item, symbols)
		}
	case Implies:
		collectStringSymbolsBoolean(value.Left, symbols)
		collectStringSymbolsBoolean(value.Right, symbols)
	case Iff:
		collectStringSymbolsBoolean(value.Left, symbols)
		collectStringSymbolsBoolean(value.Right, symbols)
	case If[BoolSort]:
		collectStringSymbolsBoolean(value.Condition, symbols)
		collectStringSymbolsBoolean(value.Then, symbols)
		collectStringSymbolsBoolean(value.Else, symbols)
	}
}

func collectStringSymbols(term any, symbols *stringSymbols) {
	switch value := term.(type) {
	case stringSymbol[StringSort]:
		symbols.add(value.iD)
	case stringConcat[StringSort]:
		for _, item := range value.values {
			collectStringSymbols(item, symbols)
		}
	case stringAt[StringSort]:
		collectStringSymbols(value.value, symbols)
	case stringSubstring[StringSort]:
		collectStringSymbols(value.value, symbols)
	case stringReplace[StringSort]:
		collectStringSymbols(value.value, symbols)
		collectStringSymbols(value.source, symbols)
		collectStringSymbols(value.replacement, symbols)
	case stringReplaceAll[StringSort]:
		collectStringSymbols(value.value, symbols)
		collectStringSymbols(value.source, symbols)
		collectStringSymbols(value.replacement, symbols)
	case integerToString[StringSort], codeToString[StringSort]:
		// Integer-valued children contain no string symbols.
	case stringLength:
		collectStringSymbols(value.value, symbols)
	case stringIndexOf:
		collectStringSymbols(value.value, symbols)
		collectStringSymbols(value.substring, symbols)
	case stringToInteger:
		collectStringSymbols(value.value, symbols)
	case stringToCode:
		collectStringSymbols(value.value, symbols)
	}
}

func stringSymbolID(term any) (int, bool) {
	value, ok := term.(stringSymbol[StringSort])
	return value.iD, ok
}

func stringModelValue(model stringModel, id int) (string, bool) {
	return model.lookup(id)
}

func setExistingString(model *stringModel, id int, value string) bool {
	for index := 0; index < model.count; index++ {
		if model.inline[index].id == id {
			if model.inline[index].value == value {
				return false
			}
			model.inline[index].value = value
			return true
		}
	}
	if _, ok := model.overflow[id]; ok {
		if model.overflow[id] == value {
			return false
		}
		model.overflow[id] = value
		return true
	}
	model.set(id, value)
	return true
}

func bindStringAssertion(term Term[BoolSort], negated bool, model *stringModel) bool {
	switch value := term.(type) {
	case Not:
		return bindStringAssertion(value.Value, !negated, model)
	case And:
		if negated {
			return false
		}
		changed := false
		for _, item := range value.Values {
			changed = bindStringAssertion(item, false, model) || changed
		}
		return changed
	case BooleanConjunction:
		if negated {
			return false
		}
		items, polarities := value.values()
		changed := false
		for index, item := range items {
			changed = bindStringAssertion(item, polarities[index], model) || changed
		}
		return changed
	case Equal:
		if !isStringTerm(value.Left) || !isStringTerm(value.Right) {
			return false
		}
		leftID, leftSymbol := stringSymbolID(value.Left)
		rightID, rightSymbol := stringSymbolID(value.Right)
		left, leftOK := evaluateString(value.Left.(Term[StringSort]), *model, integerModel{})
		right, rightOK := evaluateString(value.Right.(Term[StringSort]), *model, integerModel{})
		if !negated {
			if leftSymbol && rightOK {
				return setExistingString(model, leftID, right)
			}
			if rightSymbol && leftOK {
				return setExistingString(model, rightID, left)
			}
		} else if leftSymbol && rightSymbol && !leftOK && !rightOK {
			changed := setExistingString(model, leftID, "")
			return setExistingString(model, rightID, "a") || changed
		}
	}
	return false
}

func bindForcedStringAssertion(term Term[BoolSort], negated bool, model *stringModel) bool {
	switch value := term.(type) {
	case CompactStringWordEquation:
		if negated {
			return false
		}
		return bindCompactStringWordEquation(value, model)
	case stringSystem:
		if negated {
			return false
		}
		changed := false
		for _, relation := range value.system.relations() {
			if relation.Kind != CompactStringEqual || relation.Negated {
				continue
			}
			left, leftOK := evaluateCompactString(relation.Left, *model)
			right, rightOK := evaluateCompactString(relation.Right, *model)
			if relation.Left.Kind == compactStringSymbol && rightOK {
				changed = setExistingString(model, relation.Left.ID, right) || changed
			}
			if relation.Right.Kind == compactStringSymbol && leftOK {
				changed = setExistingString(model, relation.Right.ID, left) || changed
			}
		}
		return changed
	case Not:
		return bindForcedStringAssertion(value.Value, !negated, model)
	case And:
		if negated {
			return false
		}
		changed := false
		for _, item := range value.Values {
			changed = bindForcedStringAssertion(item, false, model) || changed
		}
		return changed
	case BooleanConjunction:
		if negated {
			return false
		}
		items, polarities := value.values()
		changed := false
		for index, item := range items {
			changed = bindForcedStringAssertion(item, polarities[index], model) || changed
		}
		return changed
	case Equal:
		if negated || !isStringTerm(value.Left) || !isStringTerm(value.Right) {
			return false
		}
		leftID, leftSymbol := stringSymbolID(value.Left)
		rightID, rightSymbol := stringSymbolID(value.Right)
		left, leftOK := evaluateString(value.Left.(Term[StringSort]), *model, integerModel{})
		right, rightOK := evaluateString(value.Right.(Term[StringSort]), *model, integerModel{})
		if leftSymbol && rightOK {
			return setExistingString(model, leftID, right)
		}
		if rightSymbol && leftOK {
			return setExistingString(model, rightID, left)
		}
		if rightOK {
			if changed, handled := bindUniquelyDelimitedStringConcat(value.Left, right, model); handled {
				return changed
			}
		}
		if leftOK {
			if changed, handled := bindUniquelyDelimitedStringConcat(value.Right, left, model); handled {
				return changed
			}
		}
	}
	return false
}

func bindUniquelyDelimitedStringConcat(term any, target string, model *stringModel) (bool, bool) {
	concat, ok := term.(stringConcat[StringSort])
	if !ok {
		return false, false
	}
	type unknownStringPart struct {
		id        int
		delimiter string
	}
	var unknowns [4]unknownStringPart
	unknownCount := 0
	literal := ""
	for _, item := range concat.values {
		if id, symbolic := stringSymbolID(item); symbolic {
			if bound, exists := model.lookup(id); exists {
				literal += bound
				continue
			}
			for index := 0; index < unknownCount; index++ {
				if unknowns[index].id == id {
					return false, false
				}
			}
			if unknownCount == len(unknowns) {
				return false, false
			}
			if unknownCount > 0 && literal == "" {
				return false, false
			}
			unknowns[unknownCount] = unknownStringPart{id: id, delimiter: literal}
			unknownCount++
			literal = ""
			continue
		}
		part, known := evaluateString(item, *model, integerModel{})
		if !known {
			return false, false
		}
		literal += part
	}
	if unknownCount == 0 {
		return false, false
	}
	prefix, suffix := unknowns[0].delimiter, literal
	if !strings.HasPrefix(target, prefix) || !strings.HasSuffix(target, suffix) ||
		len(target) < len(prefix)+len(suffix) {
		changed := false
		for index := 0; index < unknownCount; index++ {
			changed = setExistingString(model, unknowns[index].id, "") || changed
		}
		return changed, true
	}
	remaining := target[len(prefix) : len(target)-len(suffix)]
	changed := false
	for index := 1; index < unknownCount; index++ {
		delimiter := unknowns[index].delimiter
		first := strings.Index(remaining, delimiter)
		if first < 0 {
			for rest := index - 1; rest < unknownCount; rest++ {
				changed = setExistingString(model, unknowns[rest].id, "") || changed
			}
			return changed, true
		}
		if strings.LastIndex(remaining, delimiter) != first {
			return false, false
		}
		changed = setExistingString(model, unknowns[index-1].id, remaining[:first]) || changed
		remaining = remaining[first+len(delimiter):]
	}
	changed = setExistingString(model, unknowns[unknownCount-1].id, remaining) || changed
	return changed, true
}

func synthesizeStringAssertion(term Term[BoolSort], negated bool, model *stringModel) {
	switch value := term.(type) {
	case Not:
		synthesizeStringAssertion(value.Value, !negated, model)
	case And:
		if !negated {
			for _, item := range value.Values {
				synthesizeStringAssertion(item, false, model)
			}
		}
	case BooleanConjunction:
		if !negated {
			items, polarities := value.values()
			for index, item := range items {
				synthesizeStringAssertion(item, polarities[index], model)
			}
		}
	case Equal:
		length, lengthOnLeft := value.Left.(stringLength)
		integer, integerOnRight := integerConstant(value.Right)
		if !lengthOnLeft || !integerOnRight {
			length, lengthOnLeft = value.Right.(stringLength)
			integer, integerOnRight = integerConstant(value.Left)
		}
		if !negated && lengthOnLeft && integerOnRight && integer >= 0 {
			if id, ok := stringSymbolID(length.value); ok {
				if _, bound := stringModelValue(*model, id); !bound {
					setExistingString(model, id, strings.Repeat("a", int(integer)))
				}
			}
		}
	case stringContains:
		synthesizeStringPredicate(value.value, value.substring, negated, 0, model)
	case stringPrefix:
		synthesizeStringPredicate(value.value, value.prefix, negated, 1, model)
	case stringSuffix:
		synthesizeStringPredicate(value.value, value.suffix, negated, 2, model)
	case stringInRegex:
		synthesizeStringRegex(value.value, value.expression, negated, model)
	}
}

func synthesizeStringPredicate(value, part Term[StringSort], negated bool, kind int, model *stringModel) {
	id, symbolic := stringSymbolID(value)
	partValue, partOK := evaluateString(part, *model, integerModel{})
	if !symbolic || !partOK {
		return
	}
	if _, bound := stringModelValue(*model, id); bound {
		return
	}
	if negated {
		if partValue == "" {
			return
		}
		setExistingString(model, id, "")
		return
	}
	switch kind {
	case 0, 1, 2:
		setExistingString(model, id, partValue)
	}
}

func defaultUnboundStrings(symbols stringSymbols, model *stringModel) {
	for index := 0; index < symbols.count; index++ {
		id := symbols.inline[index]
		if _, bound := model.lookup(id); !bound {
			model.set(id, "")
		}
	}
	for id := range symbols.overflow {
		if _, bound := model.lookup(id); !bound {
			model.set(id, "")
		}
	}
}

func integerConstant(term any) (int64, bool) {
	switch value := term.(type) {
	case Integer:
		return value.Value, true
	case integerExact[IntSort]:
		return value.value.Int64()
	default:
		return 0, false
	}
}

func evaluateStringBoolean(term Term[BoolSort], model stringModel, integers integerModel) (bool, bool) {
	switch value := term.(type) {
	case CompactStringReplaceEquality:
		symbol, found := model.lookup(value.SymbolID)
		if !found {
			return false, false
		}
		ground, ok := groundStringReplaceEquality(value, model)
		if !ok {
			return false, false
		}
		return compactStringReplacementEquals(symbol, ground), true
	case CompactStringIndexedEquality:
		symbol, found := model.lookup(value.SymbolID)
		if !found {
			return false, false
		}
		ground, ok := groundCompactIndexedStringEquality(value, integers)
		if !ok {
			return false, false
		}
		value = ground
		var derived Term[StringSort]
		switch value.Kind {
		case CompactStringAtEquality:
			derived = StringAt(StringVal(symbol), Integer{Value: value.Offset})
		case CompactStringSubstringEquality:
			derived = StringSubstring(
				StringVal(symbol),
				Integer{Value: value.Offset},
				Integer{Value: value.Length},
			)
		default:
			return false, false
		}
		actual, known := evaluateString(derived, stringModel{}, integers)
		return actual == value.Target, known
	case *CompactGroundIndexedStringFormula:
		for index := 0; index < int(value.AssignmentCount); index++ {
			valid, known := evaluateStringBoolean(value.Assignments[index], model, integers)
			if !known || !valid {
				return valid, known
			}
		}
		for index := 0; index < int(value.EqualityCount); index++ {
			valid, known := evaluateStringBoolean(value.Equalities[index], model, integers)
			if !known || !valid {
				return valid, known
			}
		}
		return true, true
	case CompactStringIndexOfEquality:
		return evaluateCompactStringIndexOfEquality(value, model, integers)
	case *CompactGroundStringEvaluationFormula:
		for index := 0; index < int(value.StringAssignmentCount); index++ {
			if valid, known := evaluateCompactStringRelation(value.StringAssignments[index], model); !known || !valid {
				return valid, known
			}
		}
		for index := 0; index < int(value.IntegerAssignmentCount); index++ {
			if valid, known := evaluateBool(value.IntegerAssignments[index], booleanModel{}, integers, rationalModel{}); !known || !valid {
				return valid, known
			}
		}
		for index := 0; index < int(value.IndexOfCount); index++ {
			if valid, known := evaluateCompactStringIndexOfEquality(value.IndexOf[index], model, integers); !known || !valid {
				return valid, known
			}
		}
		return true, true
	case CompactStringLengthRelation:
		left, leftOK := evaluateCompactString(value.Left, model)
		right, rightOK := evaluateCompactString(value.Right, model)
		if !leftOK || !rightOK {
			return false, false
		}
		leftLength := stringCodePointCount(left)
		rightLength := stringCodePointCount(right)
		switch value.Order {
		case 0:
			return leftLength == rightLength, true
		case 1:
			return leftLength < rightLength, true
		case 2:
			return leftLength <= rightLength, true
		default:
			return false, false
		}
	case CompactStringWordEquation:
		return evaluateCompactStringWordEquation(value, model)
	case CompactStringBooleanFormula:
		return evaluateCompactStringBooleanModel(value, model)
	case stringSystem:
		for _, relation := range value.system.relations() {
			result, ok := evaluateCompactStringRelation(relation, model)
			if !ok || !result {
				return result, ok
			}
		}
		return true, true
	case Or:
		for _, item := range value.Values {
			result, ok := evaluateStringBoolean(item, model, integers)
			if !ok {
				return false, false
			}
			if result {
				return true, true
			}
		}
		return false, true
	case Implies:
		left, leftOK := evaluateStringBoolean(value.Left, model, integers)
		right, rightOK := evaluateStringBoolean(value.Right, model, integers)
		return !left || right, leftOK && rightOK
	case Iff:
		left, leftOK := evaluateStringBoolean(value.Left, model, integers)
		right, rightOK := evaluateStringBoolean(value.Right, model, integers)
		return left == right, leftOK && rightOK
	case If[BoolSort]:
		condition, ok := evaluateStringBoolean(value.Condition, model, integers)
		if !ok {
			return false, false
		}
		if condition {
			return evaluateStringBoolean(value.Then, model, integers)
		}
		return evaluateStringBoolean(value.Else, model, integers)
	case Bool:
		return value.Value, true
	case Not:
		inner, ok := evaluateStringBoolean(value.Value, model, integers)
		return !inner, ok
	case And:
		for _, item := range value.Values {
			result, ok := evaluateStringBoolean(item, model, integers)
			if !ok || !result {
				return result, ok
			}
		}
		return true, true
	case BooleanConjunction:
		items, polarities := value.values()
		for index, item := range items {
			result, ok := evaluateStringBoolean(item, model, integers)
			if !ok || result == polarities[index] {
				return false, ok
			}
		}
		return true, true
	case Equal:
		if left, ok := value.Left.(Term[StringSort]); ok {
			right, rightOK := value.Right.(Term[StringSort])
			if !rightOK {
				return false, false
			}
			leftValue, leftOK := evaluateString(left, model, integers)
			rightValue, rightValueOK := evaluateString(right, model, integers)
			return leftValue == rightValue, leftOK && rightValueOK
		}
		leftInteger, leftOK := evaluateStringIntegerExact(value.Left, model, integers)
		rightInteger, rightOK := evaluateStringIntegerExact(value.Right, model, integers)
		return CompareIntegerValue(leftInteger, rightInteger) == 0, leftOK && rightOK
	case Less:
		leftInteger, leftOK := evaluateStringIntegerExact(value.Left, model, integers)
		rightInteger, rightOK := evaluateStringIntegerExact(value.Right, model, integers)
		return CompareIntegerValue(leftInteger, rightInteger) < 0, leftOK && rightOK
	case LessEqual:
		leftInteger, leftOK := evaluateStringIntegerExact(value.Left, model, integers)
		rightInteger, rightOK := evaluateStringIntegerExact(value.Right, model, integers)
		return CompareIntegerValue(leftInteger, rightInteger) <= 0, leftOK && rightOK
	case IntegerLinearEquality:
		return evaluateBool(value, booleanModel{}, integers, rationalModel{})
	case stringContains:
		text, textOK := evaluateString(value.value, model, integers)
		part, partOK := evaluateString(value.substring, model, integers)
		return strings.Contains(text, part), textOK && partOK
	case stringPrefix:
		prefix, prefixOK := evaluateString(value.prefix, model, integers)
		text, textOK := evaluateString(value.value, model, integers)
		return strings.HasPrefix(text, prefix), prefixOK && textOK
	case stringSuffix:
		suffix, suffixOK := evaluateString(value.suffix, model, integers)
		text, textOK := evaluateString(value.value, model, integers)
		return strings.HasSuffix(text, suffix), suffixOK && textOK
	case stringIsDigit:
		text, ok := evaluateString(value.value, model, integers)
		return len(text) == 1 && text[0] >= '0' && text[0] <= '9', ok
	case stringInRegex:
		text, ok := evaluateString(value.value, model, integers)
		if !ok {
			return false, false
		}
		if witness, found := regexExpressionWitness(value.expression, model, integers); found && text == witness {
			return true, true
		}
		return matchesStringRegex(text, value.expression, model, integers)
	default:
		return false, false
	}
}

func evaluateStringInteger(term any, model stringModel, integers integerModel) (int64, bool) {
	value, ok := evaluateStringIntegerExact(term, model, integers)
	if !ok {
		return 0, false
	}
	return value.Int64()
}

func evaluateStringIntegerExact(term any, model stringModel, integers integerModel) (IntegerValue, bool) {
	if constant, ok := integerConstant(term); ok {
		return NewIntegerValue(constant), true
	}
	switch value := term.(type) {
	case stringLength:
		text, found := evaluateString(value.value, model, integers)
		return NewIntegerValue(int64(stringCodePointCount(text))), found
	case stringIndexOf:
		text, textOK := evaluateString(value.value, model, integers)
		substring, substringOK := evaluateString(value.substring, model, integers)
		offset, offsetOK := evaluateStringOffset(value.offset, integers)
		if !textOK || !substringOK || !offsetOK {
			return IntegerValue{}, false
		}
		return NewIntegerValue(stringIndexOfRunes(text, substring, offset)), true
	case stringToInteger:
		text, found := evaluateString(value.value, model, integers)
		if !found || text == "" {
			return NewIntegerValue(-1), found
		}
		for index := 0; index < len(text); index++ {
			if text[index] < '0' || text[index] > '9' {
				return NewIntegerValue(-1), true
			}
		}
		integer, err := ParseIntegerValue(text)
		return integer, err == nil
	case stringToCode:
		text, found := evaluateString(value.value, model, integers)
		if !found {
			return IntegerValue{}, false
		}
		codes := DecodeStringCodePoints(text)
		if len(codes) != 1 {
			return NewIntegerValue(-1), true
		}
		return NewIntegerValue(int64(codes[0])), true
	default:
		switch value := term.(type) {
		case Integer:
			return NewIntegerValue(value.Value), true
		case integerExact[IntSort]:
			return value.value, true
		case IntSymbol:
			return integers.lookup(value.ID)
		case integerVariable[IntSort]:
			return integers.lookup(value.iD)
		case Add:
			total := IntegerValue{}
			for _, item := range value.Values {
				next, ok := evaluateStringIntegerExact(item, model, integers)
				if !ok {
					return IntegerValue{}, false
				}
				total = AddIntegerValue(total, next)
			}
			return total, true
		case Subtract:
			left, leftOK := evaluateStringIntegerExact(value.Left, model, integers)
			right, rightOK := evaluateStringIntegerExact(value.Right, model, integers)
			return SubIntegerValue(left, right), leftOK && rightOK
		case IntegerScale:
			scaled, ok := evaluateStringIntegerExact(value.Value, model, integers)
			return MultiplyIntegerValue(value.Coefficient, scaled), ok
		case IntegerDiv:
			return evaluateInteger(value, booleanModel{}, integers, rationalModel{})
		case IntegerMod:
			return evaluateInteger(value, booleanModel{}, integers, rationalModel{})
		case If[IntSort]:
			return evaluateInteger(value, booleanModel{}, integers, rationalModel{})
		default:
			return IntegerValue{}, false
		}
	}
}

func evaluateStringOffset(term Term[IntSort], integers integerModel) (int64, bool) {
	if constant, ok := integerConstant(term); ok {
		return constant, true
	}
	return evaluateInt(term, booleanModel{}, integers, rationalModel{})
}

func evaluateStringOffsetTerm(term any, integers integerModel) (int64, bool) {
	value, ok := term.(Term[IntSort])
	if !ok {
		return 0, false
	}
	return evaluateStringOffset(value, integers)
}

func stringIndexOfRunes(text, substring string, offset int64) int64 {
	if !stringCodePointsValid(text) || !stringCodePointsValid(substring) {
		return stringIndexOfDecodedCodePoints(text, substring, offset)
	}
	if offset < 0 {
		return -1
	}
	byteOffset, codePointOffset, ok := stringCodePointByteOffset(text, offset)
	if !ok {
		return -1
	}
	if substring == "" {
		return offset
	}
	for byteIndex, codePointIndex := byteOffset, codePointOffset; byteIndex < len(text); {
		if strings.HasPrefix(text[byteIndex:], substring) &&
			stringCodePointBoundary(text, byteIndex+len(substring)) {
			return codePointIndex
		}
		byteIndex += stringCodePointWidth(text, byteIndex)
		codePointIndex++
	}
	return -1
}

func stringIndexOfDecodedCodePoints(text, substring string, offset int64) int64 {
	textRunes, substringRunes := DecodeStringCodePoints(text), DecodeStringCodePoints(substring)
	if offset < 0 || offset > int64(len(textRunes)) {
		return -1
	}
	if len(substringRunes) == 0 {
		return offset
	}
	for index := int(offset); index+len(substringRunes) <= len(textRunes); index++ {
		if string(textRunes[index:index+len(substringRunes)]) == substring {
			return int64(index)
		}
	}
	return -1
}

func stringCodePointsValid(value string) bool {
	for offset := 0; offset < len(value); {
		width := stringCodePointWidth(value, offset)
		if width == 1 && value[offset] >= 0x80 {
			return false
		}
		offset += width
	}
	return true
}

func stringCodePointByteOffset(value string, target int64) (int, int64, bool) {
	byteOffset, codePointOffset := 0, int64(0)
	for byteOffset < len(value) && codePointOffset < target {
		byteOffset += stringCodePointWidth(value, byteOffset)
		codePointOffset++
	}
	return byteOffset, codePointOffset, codePointOffset == target
}

func stringCodePointBoundary(value string, offset int) bool {
	if offset < 0 || offset > len(value) {
		return false
	}
	if offset == 0 || offset == len(value) {
		return true
	}
	return value[offset]&0xc0 != 0x80
}

func stringCodePointWidth(value string, offset int) int {
	first := value[offset]
	width := 1
	switch {
	case first < 0x80:
		return 1
	case first&0xe0 == 0xc0 && offset+2 <= len(value):
		width = 2
	case first&0xf0 == 0xe0 && offset+3 <= len(value):
		width = 3
	case first&0xf8 == 0xf0 && offset+4 <= len(value):
		width = 4
	default:
		return 1
	}
	for index := 1; index < width; index++ {
		if value[offset+index]&0xc0 != 0x80 {
			return 1
		}
	}
	return width
}
