package smt

import "strings"

// CompactStringPattern is a bounded literal-delimited sequence of string
// symbols. Delimiters[0] is the prefix, Delimiters[Count] the suffix, and the
// intervening entries separate adjacent symbols.
type CompactStringPattern struct {
	Count       int
	SymbolIDs   [4]int
	SymbolNames [4]string
	Delimiters  [5]string
}

// CompactStringWordEquation equates a bounded symbolic pattern with a ground
// target. Standalone solving searches all bounded splits; conjunction
// propagation only commits uniquely forced splits.
type CompactStringWordEquation struct {
	Pattern CompactStringPattern
	Target  string
}

func (CompactStringWordEquation) isTerm(BoolSort) {}

type boundedWordEquationLength struct {
	id         int
	minimum    int64
	maximum    int64
	hasMaximum bool
}

type boundedWordEquationConstraints struct {
	model       stringModel
	lengthCount int
	lengths     [4]boundedWordEquationLength
}

func solveBoundedWordEquationConjunction(assertions []Term[BoolSort]) (checkOutcome, bool) {
	var conjuncts [8]Term[BoolSort]
	count := 0
	for _, assertion := range assertions {
		if !appendBoundedWordEquationConjunct(assertion, &conjuncts, &count) {
			return checkOutcome{}, false
		}
	}
	var equations [4]CompactStringWordEquation
	var equationConjuncts [8]bool
	equationCount := 0
	for index := 0; index < count; index++ {
		if candidate, ok := compactStringWordEquationFromTerm(conjuncts[index]); ok {
			if equationCount == len(equations) {
				return checkOutcome{}, false
			}
			equations[equationCount] = candidate
			equationCount++
			equationConjuncts[index] = true
		}
	}
	if equationCount == 0 {
		return checkOutcome{}, false
	}
	var constraints boundedWordEquationConstraints
	for index := 0; index < count; index++ {
		if equationConjuncts[index] {
			continue
		}
		recognized, contradiction := bindBoundedWordEquationGroundConjunct(conjuncts[index], &constraints)
		if !recognized {
			return checkOutcome{}, false
		}
		if contradiction {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	for index := 0; index < constraints.lengthCount; index++ {
		found := false
		for equationIndex := 0; equationIndex < equationCount; equationIndex++ {
			found = found || compactStringPatternContainsID(
				equations[equationIndex].Pattern, constraints.lengths[index].id,
			)
		}
		if !found {
			return checkOutcome{}, false
		}
	}
	steps := 0
	model, found, complete := searchCompactStringWordEquationSystem(
		equations, equationCount, 0, 0, 0, constraints, &steps,
	)
	if !complete {
		return checkOutcome{
			status: checkUnknown,
			reason: ResourceLimit{Limit: compactStringWordEquationSearchLimit},
		}, true
	}
	if !found {
		return checkOutcome{status: checkUnsat}, true
	}
	for index := 0; index < count; index++ {
		value, complete := evaluateStringBoolean(conjuncts[index], model, integerModel{})
		if !complete || !value {
			return checkOutcome{}, false
		}
	}
	return checkOutcome{status: checkSat, strings: model}, true
}

func appendBoundedWordEquationConjunct(term Term[BoolSort], result *[8]Term[BoolSort], count *int) bool {
	switch value := term.(type) {
	case And:
		for _, child := range value.Values {
			if !appendBoundedWordEquationConjunct(child, result, count) {
				return false
			}
		}
		return true
	case BooleanConjunction:
		children, negated := value.values()
		for index, child := range children {
			if negated[index] || !appendBoundedWordEquationConjunct(child, result, count) {
				return false
			}
		}
		return true
	default:
		if *count == len(result) {
			return false
		}
		result[*count] = term
		*count++
		return true
	}
}

func compactStringWordEquationFromTerm(term Term[BoolSort]) (CompactStringWordEquation, bool) {
	if equation, ok := term.(CompactStringWordEquation); ok {
		return equation, true
	}
	equality, ok := term.(Equal)
	if !ok || !isStringTerm(equality.Left) || !isStringTerm(equality.Right) {
		return CompactStringWordEquation{}, false
	}
	if target, ground := evaluateString(equality.Right.(Term[StringSort]), stringModel{}, integerModel{}); ground {
		if pattern, ok := compactPatternFromStringTerm(equality.Left); ok {
			return CompactStringWordEquation{Pattern: pattern, Target: target}, true
		}
	}
	if target, ground := evaluateString(equality.Left.(Term[StringSort]), stringModel{}, integerModel{}); ground {
		if pattern, ok := compactPatternFromStringTerm(equality.Right); ok {
			return CompactStringWordEquation{Pattern: pattern, Target: target}, true
		}
	}
	return CompactStringWordEquation{}, false
}

func bindBoundedWordEquationGroundConjunct(term Term[BoolSort], constraints *boundedWordEquationConstraints) (bool, bool) {
	switch value := term.(type) {
	case Bool:
		return true, !value.Value
	case Equal:
		if id, length, ok := boundedWordEquationLengthEquality(value); ok {
			return assignBoundedWordEquationLength(constraints, id, length)
		}
		if !isStringTerm(value.Left) || !isStringTerm(value.Right) {
			return false, false
		}
		if id, symbol := stringSymbolID(value.Left); symbol {
			if ground, ok := evaluateString(value.Right.(Term[StringSort]), stringModel{}, integerModel{}); ok {
				return assignBoundedWordEquationGroundValue(constraints, id, ground)
			}
		}
		if id, symbol := stringSymbolID(value.Right); symbol {
			if ground, ok := evaluateString(value.Left.(Term[StringSort]), stringModel{}, integerModel{}); ok {
				return assignBoundedWordEquationGroundValue(constraints, id, ground)
			}
		}
		return false, false
	case Less:
		id, minimum, maximum, hasMaximum, ok := boundedWordEquationLengthComparison(value.Left, value.Right, true)
		if !ok {
			return false, false
		}
		return assignBoundedWordEquationLengthRange(constraints, id, minimum, maximum, hasMaximum)
	case LessEqual:
		id, minimum, maximum, hasMaximum, ok := boundedWordEquationLengthComparison(value.Left, value.Right, false)
		if !ok {
			return false, false
		}
		return assignBoundedWordEquationLengthRange(constraints, id, minimum, maximum, hasMaximum)
	case stringSystem:
		for _, relation := range value.system.relations() {
			if relation.Negated &&
				relation.Kind != CompactStringLengthLess &&
				relation.Kind != CompactStringLengthLessEqual {
				return false, false
			}
			if relation.Kind == CompactStringEqual {
				if relation.Left.Kind == compactStringSymbol && relation.Right.Kind == compactStringLiteral {
					if _, contradiction := assignBoundedWordEquationGroundValue(constraints, relation.Left.ID, relation.Right.Value); contradiction {
						return true, true
					}
					continue
				}
				if relation.Right.Kind == compactStringSymbol && relation.Left.Kind == compactStringLiteral {
					if _, contradiction := assignBoundedWordEquationGroundValue(constraints, relation.Right.ID, relation.Left.Value); contradiction {
						return true, true
					}
					continue
				}
			}
			if relation.Kind == CompactStringLengthEqual && !relation.Negated &&
				relation.Left.Kind == compactStringSymbol {
				if _, contradiction := assignBoundedWordEquationLength(constraints, relation.Left.ID, relation.Integer); contradiction {
					return true, true
				}
				continue
			}
			if (relation.Kind == CompactStringLengthLess || relation.Kind == CompactStringLengthLessEqual) &&
				relation.Left.Kind == compactStringSymbol {
				minimum, maximum, hasMaximum := compactStringLengthRange(relation)
				if _, contradiction := assignBoundedWordEquationLengthRange(
					constraints, relation.Left.ID, minimum, maximum, hasMaximum,
				); contradiction {
					return true, true
				}
				continue
			}
			return false, false
		}
		return true, false
	default:
		return false, false
	}
}

func compactStringLengthRange(relation CompactStringRelation) (minimum, maximum int64, hasMaximum bool) {
	minimum, maximum, hasMaximum = 0, relation.Integer, true
	if relation.Negated {
		minimum, hasMaximum = relation.Integer, false
		if relation.Kind == CompactStringLengthLessEqual && minimum < 1<<63-1 {
			minimum++
		}
	} else if relation.Kind == CompactStringLengthLess && maximum > -1<<63 {
		maximum--
	}
	return
}

func assignBoundedWordEquationGroundValue(constraints *boundedWordEquationConstraints, id int, value string) (bool, bool) {
	if existing, found := constraints.model.lookup(id); found {
		return true, existing != value
	}
	if length, found := constraints.length(id); found && !length.allows(int64(stringCodePointCount(value))) {
		return true, true
	}
	constraints.model.set(id, value)
	return true, false
}

func boundedWordEquationLengthEquality(equality Equal) (int, int64, bool) {
	if length, ok := equality.Left.(stringLength); ok {
		if symbol, ok := length.value.(stringSymbol[StringSort]); ok {
			value, constant := integerConstant(equality.Right)
			return symbol.iD, value, constant
		}
	}
	if length, ok := equality.Right.(stringLength); ok {
		if symbol, ok := length.value.(stringSymbol[StringSort]); ok {
			value, constant := integerConstant(equality.Left)
			return symbol.iD, value, constant
		}
	}
	return 0, 0, false
}

func boundedWordEquationLengthComparison(
	left, right Term[IntSort],
	strict bool,
) (id int, minimum, maximum int64, hasMaximum, ok bool) {
	if length, lengthOnLeft := left.(stringLength); lengthOnLeft {
		if symbol, symbolic := length.value.(stringSymbol[StringSort]); symbolic {
			if constant, ground := integerConstant(right); ground {
				maximum = constant
				if strict && maximum > -1<<63 {
					maximum--
				}
				return symbol.iD, 0, maximum, true, true
			}
		}
	}
	if length, lengthOnRight := right.(stringLength); lengthOnRight {
		if symbol, symbolic := length.value.(stringSymbol[StringSort]); symbolic {
			if constant, ground := integerConstant(left); ground {
				minimum = constant
				if strict && minimum < 1<<63-1 {
					minimum++
				}
				if minimum < 0 {
					minimum = 0
				}
				return symbol.iD, minimum, 0, false, true
			}
		}
	}
	return 0, 0, 0, false, false
}

func assignBoundedWordEquationLength(constraints *boundedWordEquationConstraints, id int, length int64) (bool, bool) {
	if length < 0 {
		return true, true
	}
	return assignBoundedWordEquationLengthRange(constraints, id, length, length, true)
}

func assignBoundedWordEquationLengthRange(
	constraints *boundedWordEquationConstraints,
	id int,
	minimum, maximum int64,
	hasMaximum bool,
) (bool, bool) {
	if minimum < 0 {
		minimum = 0
	}
	if hasMaximum && maximum < minimum {
		return true, true
	}
	if existing, found := constraints.length(id); found {
		if existing.minimum > minimum {
			minimum = existing.minimum
		}
		if existing.hasMaximum && (!hasMaximum || existing.maximum < maximum) {
			maximum, hasMaximum = existing.maximum, true
		}
		if hasMaximum && maximum < minimum {
			return true, true
		}
		for index := 0; index < constraints.lengthCount; index++ {
			if constraints.lengths[index].id == id {
				constraints.lengths[index] = boundedWordEquationLength{
					id: id, minimum: minimum, maximum: maximum, hasMaximum: hasMaximum,
				}
				if value, bound := constraints.model.lookup(id); bound &&
					!constraints.lengths[index].allows(int64(stringCodePointCount(value))) {
					return true, true
				}
				return true, false
			}
		}
	}
	constraint := boundedWordEquationLength{
		id: id, minimum: minimum, maximum: maximum, hasMaximum: hasMaximum,
	}
	if value, found := constraints.model.lookup(id); found &&
		!constraint.allows(int64(stringCodePointCount(value))) {
		return true, true
	}
	if constraints.lengthCount == len(constraints.lengths) {
		return false, false
	}
	constraints.lengths[constraints.lengthCount] = constraint
	constraints.lengthCount++
	return true, false
}

func (constraints boundedWordEquationConstraints) length(id int) (boundedWordEquationLength, bool) {
	for index := 0; index < constraints.lengthCount; index++ {
		if constraints.lengths[index].id == id {
			return constraints.lengths[index], true
		}
	}
	return boundedWordEquationLength{}, false
}

func (constraint boundedWordEquationLength) allows(length int64) bool {
	return length >= constraint.minimum && (!constraint.hasMaximum || length <= constraint.maximum)
}

func compactStringPatternContainsID(pattern CompactStringPattern, id int) bool {
	for index := 0; index < pattern.Count; index++ {
		if pattern.SymbolIDs[index] == id {
			return true
		}
	}
	return false
}

func solveCompactStringWordEquationAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if len(assertions) != 1 {
		return checkOutcome{}, false
	}
	equation, ok := assertions[0].(CompactStringWordEquation)
	if !ok {
		return checkOutcome{}, false
	}
	return solveCompactStringWordEquation(equation, false)
}

func solveBoundedGroundWordEquationAssertion(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if len(assertions) != 1 {
		return checkOutcome{}, false
	}
	equality, ok := assertions[0].(Equal)
	if !ok || !isStringTerm(equality.Left) || !isStringTerm(equality.Right) {
		return checkOutcome{}, false
	}
	if target, ground := evaluateString(equality.Right.(Term[StringSort]), stringModel{}, integerModel{}); ground {
		if pattern, ok := compactPatternFromStringTerm(equality.Left); ok {
			return solveCompactStringWordEquation(CompactStringWordEquation{Pattern: pattern, Target: target}, false)
		}
	}
	if target, ground := evaluateString(equality.Left.(Term[StringSort]), stringModel{}, integerModel{}); ground {
		if pattern, ok := compactPatternFromStringTerm(equality.Right); ok {
			return solveCompactStringWordEquation(CompactStringWordEquation{Pattern: pattern, Target: target}, false)
		}
	}
	return checkOutcome{}, false
}

func compactPatternFromStringTerm(term any) (CompactStringPattern, bool) {
	concat, ok := term.(stringConcat[StringSort])
	if !ok {
		return CompactStringPattern{}, false
	}
	var pattern CompactStringPattern
	literal := ""
	for _, item := range concat.values {
		if symbol, ok := item.(stringSymbol[StringSort]); ok {
			if pattern.Count == len(pattern.SymbolIDs) {
				return CompactStringPattern{}, false
			}
			pattern.Delimiters[pattern.Count] = literal
			pattern.SymbolIDs[pattern.Count] = symbol.iD
			pattern.SymbolNames[pattern.Count] = symbol.name
			pattern.Count++
			literal = ""
			continue
		}
		value, ground := evaluateString(item, stringModel{}, integerModel{})
		if !ground {
			return CompactStringPattern{}, false
		}
		literal += value
	}
	if pattern.Count == 0 {
		return CompactStringPattern{}, false
	}
	pattern.Delimiters[pattern.Count] = literal
	return pattern, true
}

func solveCompactStringWordEquation(equation CompactStringWordEquation, requireUnique bool) (checkOutcome, bool) {
	pattern := equation.Pattern
	if pattern.Count < 1 || pattern.Count > len(pattern.SymbolIDs) {
		return checkOutcome{}, false
	}
	if !requireUnique {
		steps := 0
		model, found, complete := searchCompactStringWordEquation(
			pattern, equation.Target, 0, 0, boundedWordEquationConstraints{}, &steps,
		)
		if !complete {
			return checkOutcome{
				status: checkUnknown,
				reason: ResourceLimit{Limit: compactStringWordEquationSearchLimit},
			}, true
		}
		if !found {
			return checkOutcome{status: checkUnsat}, true
		}
		return checkOutcome{status: checkSat, strings: model}, true
	}
	for index := 0; index < pattern.Count; index++ {
		for previous := 0; previous < index; previous++ {
			if pattern.SymbolIDs[previous] == pattern.SymbolIDs[index] {
				return checkOutcome{}, false
			}
		}
	}
	prefix, suffix := pattern.Delimiters[0], pattern.Delimiters[pattern.Count]
	if !strings.HasPrefix(equation.Target, prefix) ||
		!strings.HasSuffix(equation.Target, suffix) ||
		len(equation.Target) < len(prefix)+len(suffix) {
		return checkOutcome{status: checkUnsat}, true
	}
	remaining := equation.Target[len(prefix) : len(equation.Target)-len(suffix)]
	var model stringModel
	for index := 1; index < pattern.Count; index++ {
		delimiter := pattern.Delimiters[index]
		if delimiter == "" {
			return checkOutcome{}, false
		}
		first := strings.Index(remaining, delimiter)
		if first < 0 {
			return checkOutcome{status: checkUnsat}, true
		}
		if strings.LastIndex(remaining, delimiter) != first {
			return checkOutcome{}, false
		}
		model.set(pattern.SymbolIDs[index-1], remaining[:first])
		remaining = remaining[first+len(delimiter):]
	}
	model.set(pattern.SymbolIDs[pattern.Count-1], remaining)
	return checkOutcome{status: checkSat, strings: model}, true
}

const compactStringWordEquationSearchLimit = 4096

func searchCompactStringWordEquation(
	pattern CompactStringPattern,
	target string,
	index, offset int,
	constraints boundedWordEquationConstraints,
	steps *int,
) (stringModel, bool, bool) {
	equations := [4]CompactStringWordEquation{{
		Pattern: pattern,
		Target:  target,
	}}
	return searchCompactStringWordEquationSystem(
		equations, 1, 0, index, offset, constraints, steps,
	)
}

func searchCompactStringWordEquationSystem(
	equations [4]CompactStringWordEquation,
	equationCount, equationIndex, index, offset int,
	constraints boundedWordEquationConstraints,
	steps *int,
) (stringModel, bool, bool) {
	if equationIndex == equationCount {
		return constraints.model, true, true
	}
	*steps++
	if *steps > compactStringWordEquationSearchLimit {
		return stringModel{}, false, false
	}
	equation := equations[equationIndex]
	pattern, target := equation.Pattern, equation.Target
	if pattern.Count < 1 || pattern.Count > len(pattern.SymbolIDs) {
		return stringModel{}, false, true
	}
	delimiter := pattern.Delimiters[index]
	if offset > len(target) || !strings.HasPrefix(target[offset:], delimiter) {
		return stringModel{}, false, true
	}
	offset += len(delimiter)
	if index == pattern.Count {
		if offset != len(target) {
			return stringModel{}, false, true
		}
		return searchCompactStringWordEquationSystem(
			equations, equationCount, equationIndex+1, 0, 0, constraints, steps,
		)
	}
	id := pattern.SymbolIDs[index]
	if value, bound := constraints.model.lookup(id); bound {
		if !strings.HasPrefix(target[offset:], value) {
			return stringModel{}, false, true
		}
		return searchCompactStringWordEquationSystem(
			equations, equationCount, equationIndex, index+1, offset+len(value), constraints, steps,
		)
	}
	for end := offset; end <= len(target); end++ {
		if !stringWordEquationBoundary(target, end) {
			continue
		}
		value := target[offset:end]
		if length, constrained := constraints.length(id); constrained &&
			!length.allows(int64(stringCodePointCount(value))) {
			continue
		}
		candidate := constraints
		candidate.model.set(id, value)
		result, found, complete := searchCompactStringWordEquationSystem(
			equations, equationCount, equationIndex, index+1, end, candidate, steps,
		)
		if !complete {
			return stringModel{}, false, false
		}
		if found {
			return result, true, true
		}
	}
	return stringModel{}, false, true
}

func stringWordEquationBoundary(value string, offset int) bool {
	return offset == 0 || offset == len(value) || value[offset]&0xc0 != 0x80
}

func stringCodePointCount(value string) int {
	count := 0
	for offset := 0; offset < len(value); count++ {
		first := value[offset]
		width := 1
		switch {
		case first < 0x80:
		case first&0xe0 == 0xc0:
			width = 2
		case first&0xf0 == 0xe0:
			width = 3
		case first&0xf8 == 0xf0:
			width = 4
		}
		if offset+width > len(value) {
			offset++
			continue
		}
		valid := true
		for index := 1; index < width; index++ {
			if value[offset+index]&0xc0 != 0x80 {
				valid = false
				break
			}
		}
		if valid {
			offset += width
		} else {
			offset++
		}
	}
	return count
}

func bindCompactStringWordEquation(equation CompactStringWordEquation, model *stringModel) bool {
	source := equation.Pattern
	if source.Count < 1 || source.Count > len(source.SymbolIDs) {
		return false
	}
	var reduced CompactStringPattern
	literal := source.Delimiters[0]
	for index := 0; index < source.Count; index++ {
		if bound, ok := model.lookup(source.SymbolIDs[index]); ok {
			literal += bound
			literal += source.Delimiters[index+1]
			continue
		}
		reduced.Delimiters[reduced.Count] = literal
		reduced.SymbolIDs[reduced.Count] = source.SymbolIDs[index]
		reduced.SymbolNames[reduced.Count] = source.SymbolNames[index]
		reduced.Count++
		literal = source.Delimiters[index+1]
	}
	if reduced.Count == 0 {
		return false
	}
	reduced.Delimiters[reduced.Count] = literal
	outcome, recognized := solveCompactStringWordEquation(CompactStringWordEquation{
		Pattern: reduced,
		Target:  equation.Target,
	}, true)
	if !recognized || outcome.status != checkSat {
		return false
	}
	changed := false
	for index := 0; index < reduced.Count; index++ {
		value, ok := outcome.strings.lookup(reduced.SymbolIDs[index])
		if ok {
			changed = setExistingString(model, reduced.SymbolIDs[index], value) || changed
		}
	}
	return changed
}

func evaluateCompactStringWordEquation(equation CompactStringWordEquation, model stringModel) (bool, bool) {
	pattern := equation.Pattern
	if pattern.Count < 1 || pattern.Count > len(pattern.SymbolIDs) {
		return false, false
	}
	offset := 0
	for index := 0; index < pattern.Count; index++ {
		delimiter := pattern.Delimiters[index]
		if !strings.HasPrefix(equation.Target[offset:], delimiter) {
			return false, true
		}
		offset += len(delimiter)
		value, ok := model.lookup(pattern.SymbolIDs[index])
		if !ok {
			return false, false
		}
		if !strings.HasPrefix(equation.Target[offset:], value) {
			return false, true
		}
		offset += len(value)
	}
	suffix := pattern.Delimiters[pattern.Count]
	return offset+len(suffix) == len(equation.Target) &&
		equation.Target[offset:] == suffix, true
}

func CompactStringWordEquationValue(model Model, equation CompactStringWordEquation) (bool, bool) {
	return evaluateCompactStringWordEquation(equation, model.strings)
}
