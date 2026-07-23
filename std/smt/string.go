package smt

import (
	"strings"
	"unicode/utf8"
)

const (
	compactStringLiteral = iota
	compactStringSymbol
)

const (
	CompactStringEqual = iota
	CompactStringLengthEqual
	CompactStringContains
	CompactStringPrefix
	CompactStringSuffix
)

type CompactStringTerm struct {
	Kind  uint8
	ID    int
	Name  string
	Value string
}

type CompactStringRelation struct {
	Kind    uint8
	Negated bool
	Left    CompactStringTerm
	Right   CompactStringTerm
	Integer int64
}

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
		runes := DecodeStringCodePoints(text)
		if index < 0 || index >= int64(len(runes)) {
			return "", true
		}
		return string(runes[index]), true
	case stringSubstring[StringSort]:
		text, textOK := evaluateString(value.value, model, integers)
		offset, offsetOK := evaluateStringOffset(value.offset, integers)
		length, lengthOK := evaluateStringOffset(value.length, integers)
		if !textOK || !offsetOK || !lengthOK {
			return "", false
		}
		runes := DecodeStringCodePoints(text)
		if offset < 0 || offset >= int64(len(runes)) || length <= 0 {
			return "", true
		}
		end := offset + length
		if end < offset || end > int64(len(runes)) {
			end = int64(len(runes))
		}
		return string(runes[offset:end]), true
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
	case stringContains, stringPrefix, stringSuffix, stringIsDigit, stringInRegex, stringSystem:
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
		if relation.Left.Kind == compactStringLiteral && (relation.Kind == CompactStringLengthEqual || relation.Right.Kind == compactStringLiteral) {
			if value, complete := evaluateCompactStringRelation(relation, stringModel{}); complete && !value {
				return checkOutcome{status: checkUnsat}, true
			}
		}
		if relation.Kind == CompactStringLengthEqual && !relation.Negated && relation.Integer < 0 {
			return checkOutcome{status: checkUnsat}, true
		}
		if relation.Left.Kind == compactStringSymbol {
			symbols.add(relation.Left.ID)
		}
		if relation.Right.Kind == compactStringSymbol {
			symbols.add(relation.Right.ID)
		}
	}
	for pass := 0; pass < len(relations)+1; pass++ {
		changed := false
		for _, relation := range relations {
			if relation.Kind != CompactStringEqual || relation.Negated {
				continue
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
	for _, relation := range relations {
		if relation.Kind != CompactStringLengthEqual || relation.Negated || relation.Integer < 0 || relation.Left.Kind != compactStringSymbol {
			continue
		}
		if _, bound := model.lookup(relation.Left.ID); !bound {
			setExistingString(&model, relation.Left.ID, strings.Repeat("a", int(relation.Integer)))
		}
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
	return "", false
}

func evaluateCompactStringRelation(relation CompactStringRelation, model stringModel) (bool, bool) {
	left, leftOK := evaluateCompactString(relation.Left, model)
	result, complete := false, leftOK
	switch relation.Kind {
	case CompactStringEqual:
		right, rightOK := evaluateCompactString(relation.Right, model)
		result, complete = left == right, leftOK && rightOK
	case CompactStringLengthEqual:
		result = int64(len(DecodeStringCodePoints(left))) == relation.Integer
	case CompactStringContains:
		right, rightOK := evaluateCompactString(relation.Right, model)
		result, complete = strings.Contains(left, right), leftOK && rightOK
	case CompactStringPrefix:
		right, rightOK := evaluateCompactString(relation.Right, model)
		result, complete = strings.HasPrefix(left, right), leftOK && rightOK
	case CompactStringSuffix:
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

func collectStringSymbolsBoolean(term Term[BoolSort], symbols *stringSymbols) {
	switch value := term.(type) {
	case stringSystem:
		for _, relation := range value.system.relations() {
			if relation.Left.Kind == compactStringSymbol {
				symbols.add(relation.Left.ID)
			}
			if relation.Right.Kind == compactStringSymbol {
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
	}
	return false
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
	case stringSystem:
		for _, relation := range value.system.relations() {
			result, ok := evaluateCompactStringRelation(relation, model)
			if !ok || !result {
				return result, ok
			}
		}
		return true, true
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
		return NewIntegerValue(int64(len(DecodeStringCodePoints(text)))), found
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
			return evaluateInteger(value, booleanModel{}, integers, rationalModel{})
		case Subtract:
			return evaluateInteger(value, booleanModel{}, integers, rationalModel{})
		case IntegerScale:
			return evaluateInteger(value, booleanModel{}, integers, rationalModel{})
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
