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
// target. Ambiguous empty or repeated delimiters remain unsupported.
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
	return solveCompactStringWordEquation(equation)
}

func solveCompactStringWordEquation(equation CompactStringWordEquation) (checkOutcome, bool) {
	pattern := equation.Pattern
	if pattern.Count < 1 || pattern.Count > len(pattern.SymbolIDs) {
		return checkOutcome{}, false
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
	})
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
