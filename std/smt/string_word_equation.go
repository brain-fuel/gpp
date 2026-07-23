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
		model, found, complete := searchCompactStringWordEquation(pattern, equation.Target, 0, 0, stringModel{}, &steps)
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
	model stringModel,
	steps *int,
) (stringModel, bool, bool) {
	*steps++
	if *steps > compactStringWordEquationSearchLimit {
		return stringModel{}, false, false
	}
	delimiter := pattern.Delimiters[index]
	if offset > len(target) || !strings.HasPrefix(target[offset:], delimiter) {
		return stringModel{}, false, true
	}
	offset += len(delimiter)
	if index == pattern.Count {
		return model, offset == len(target), true
	}
	id := pattern.SymbolIDs[index]
	if value, bound := model.lookup(id); bound {
		if !strings.HasPrefix(target[offset:], value) {
			return stringModel{}, false, true
		}
		return searchCompactStringWordEquation(pattern, target, index+1, offset+len(value), model, steps)
	}
	for end := offset; end <= len(target); end++ {
		if !stringWordEquationBoundary(target, end) {
			continue
		}
		candidate := model
		candidate.set(id, target[offset:end])
		result, found, complete := searchCompactStringWordEquation(pattern, target, index+1, end, candidate, steps)
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
