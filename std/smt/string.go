package smt

import (
	"strings"
	"unicode/utf8"
)

type stringModelEntry struct {
	id    int
	value string
}

type stringModel struct {
	count    int
	inline   [4]stringModelEntry
	overflow map[int]string
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

func evaluateString(term Term[StringSort], model stringModel) (string, bool) {
	switch value := term.(type) {
	case stringValue[StringSort]:
		return value.value, true
	case stringSymbol[StringSort]:
		return model.lookup(value.iD)
	case stringConcat[StringSort]:
		var result strings.Builder
		for _, item := range value.values {
			part, ok := evaluateString(item, model)
			if !ok {
				return "", false
			}
			result.WriteString(part)
		}
		return result.String(), true
	default:
		return "", false
	}
}

func evaluateBoolWithStringsAndDatatypes(term Term[BoolSort], booleans booleanModel, integers integerModel, reals rationalModel, strings stringModel, datatypes *datatypeModel) (bool, bool) {
	if containsStringTheory(term) {
		return evaluateStringBoolean(term, strings)
	}
	return evaluateBoolWithDatatypes(term, booleans, integers, reals, datatypes)
}

func containsStringTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case stringContains, stringPrefix, stringSuffix:
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
	case stringValue[StringSort], stringSymbol[StringSort], stringConcat[StringSort]:
		return true
	default:
		return false
	}
}

func isStringIntegerTerm(term any) bool {
	_, ok := term.(stringLength)
	return ok
}

func solveStringAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	var model stringModel
	var symbols stringSymbols
	for _, assertion := range assertions {
		if value, ground := evaluateStringBoolean(assertion, stringModel{}); ground && !value {
			return checkOutcome{status: checkUnsat}, true
		}
		collectStringSymbolsBoolean(assertion, &symbols)
	}
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
		value, ok := evaluateStringBoolean(assertion, model)
		if !ok {
			return checkOutcome{}, false
		}
		if !value {
			// A failed synthesized candidate is not, by itself, an
			// unsatisfiability proof. Ground formulas are complete; symbolic
			// formulas outside the constructive fragment must remain unknown.
			if symbols.count == 0 && len(symbols.overflow) == 0 {
				return checkOutcome{status: checkUnsat}, true
			}
			return checkOutcome{}, false
		}
	}
	return checkOutcome{status: checkSat, strings: model}, true
}

func collectStringSymbolsBoolean(term Term[BoolSort], symbols *stringSymbols) {
	switch value := term.(type) {
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
	case stringLength:
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
		left, leftOK := evaluateString(value.Left.(Term[StringSort]), *model)
		right, rightOK := evaluateString(value.Right.(Term[StringSort]), *model)
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
	}
}

func synthesizeStringPredicate(value, part Term[StringSort], negated bool, kind int, model *stringModel) {
	id, symbolic := stringSymbolID(value)
	partValue, partOK := evaluateString(part, *model)
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

func evaluateStringBoolean(term Term[BoolSort], model stringModel) (bool, bool) {
	switch value := term.(type) {
	case Bool:
		return value.Value, true
	case Not:
		inner, ok := evaluateStringBoolean(value.Value, model)
		return !inner, ok
	case And:
		for _, item := range value.Values {
			result, ok := evaluateStringBoolean(item, model)
			if !ok || !result {
				return result, ok
			}
		}
		return true, true
	case BooleanConjunction:
		items, polarities := value.values()
		for index, item := range items {
			result, ok := evaluateStringBoolean(item, model)
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
			leftValue, leftOK := evaluateString(left, model)
			rightValue, rightValueOK := evaluateString(right, model)
			return leftValue == rightValue, leftOK && rightValueOK
		}
		leftLength, leftOK := evaluateStringInteger(value.Left, model)
		rightLength, rightOK := evaluateStringInteger(value.Right, model)
		return leftLength == rightLength, leftOK && rightOK
	case stringContains:
		text, textOK := evaluateString(value.value, model)
		part, partOK := evaluateString(value.substring, model)
		return strings.Contains(text, part), textOK && partOK
	case stringPrefix:
		prefix, prefixOK := evaluateString(value.prefix, model)
		text, textOK := evaluateString(value.value, model)
		return strings.HasPrefix(text, prefix), prefixOK && textOK
	case stringSuffix:
		suffix, suffixOK := evaluateString(value.suffix, model)
		text, textOK := evaluateString(value.value, model)
		return strings.HasSuffix(text, suffix), suffixOK && textOK
	default:
		return false, false
	}
}

func evaluateStringInteger(term any, model stringModel) (int64, bool) {
	if constant, ok := integerConstant(term); ok {
		return constant, true
	}
	length, ok := term.(stringLength)
	if !ok {
		return 0, false
	}
	value, found := evaluateString(length.value, model)
	return int64(utf8.RuneCountInString(value)), found
}
