package smt

const (
	compactStringBooleanFalse uint8 = 240 + iota
	compactStringBooleanTrue
	compactStringBooleanNot
	compactStringBooleanAnd
	compactStringBooleanOr
)

type CompactStringRegexLiteralAtom struct {
	SymbolID   int
	SymbolName string
	Literal    string
}

// CompactStringBooleanFormula is an allocation-free postfix formula over up
// to four singleton-regex membership atoms. Larger formulas use the general
// Boolean and regular-expression terms.
type CompactStringBooleanFormula struct {
	AtomCount int
	NodeCount int
	Atoms     [4]CompactStringRegexLiteralAtom
	Nodes     [32]uint8
}

func (CompactStringBooleanFormula) isTerm(BoolSort) {}

func CompactStringRegexLiteralFormula(symbol CompactStringTerm, literal string) (CompactStringBooleanFormula, bool) {
	if symbol.Kind != compactStringSymbol {
		return CompactStringBooleanFormula{}, false
	}
	var result CompactStringBooleanFormula
	result.AtomCount, result.NodeCount = 1, 1
	result.Atoms[0] = CompactStringRegexLiteralAtom{
		SymbolID: symbol.ID, SymbolName: symbol.Name, Literal: literal,
	}
	return result, true
}

func CompactStringBooleanConstant(value bool) CompactStringBooleanFormula {
	var result CompactStringBooleanFormula
	result.NodeCount = 1
	result.Nodes[0] = compactStringBooleanFalse
	if value {
		result.Nodes[0] = compactStringBooleanTrue
	}
	return result
}

func CompactStringBooleanNotFormula(value CompactStringBooleanFormula) (CompactStringBooleanFormula, bool) {
	if value.NodeCount == 0 || value.NodeCount == len(value.Nodes) {
		return CompactStringBooleanFormula{}, false
	}
	value.Nodes[value.NodeCount] = compactStringBooleanNot
	value.NodeCount++
	return value, true
}

func CompactStringBooleanAndFormula(left, right CompactStringBooleanFormula) (CompactStringBooleanFormula, bool) {
	return combineCompactStringBooleanFormula(left, right, compactStringBooleanAnd)
}

func CompactStringBooleanOrFormula(left, right CompactStringBooleanFormula) (CompactStringBooleanFormula, bool) {
	return combineCompactStringBooleanFormula(left, right, compactStringBooleanOr)
}

func combineCompactStringBooleanFormula(left, right CompactStringBooleanFormula, operator uint8) (CompactStringBooleanFormula, bool) {
	if left.NodeCount == 0 || right.NodeCount == 0 ||
		left.NodeCount+right.NodeCount+1 > len(left.Nodes) {
		return CompactStringBooleanFormula{}, false
	}
	result := left
	var remap [4]uint8
	for index := 0; index < right.AtomCount; index++ {
		atom := right.Atoms[index]
		target := -1
		for existing := 0; existing < result.AtomCount; existing++ {
			if result.Atoms[existing] == atom {
				target = existing
				break
			}
		}
		if target < 0 {
			if result.AtomCount == len(result.Atoms) {
				return CompactStringBooleanFormula{}, false
			}
			target = result.AtomCount
			result.Atoms[target] = atom
			result.AtomCount++
		}
		remap[index] = uint8(target)
	}
	for index := 0; index < right.NodeCount; index++ {
		node := right.Nodes[index]
		if node < uint8(right.AtomCount) {
			node = remap[node]
		}
		result.Nodes[result.NodeCount] = node
		result.NodeCount++
	}
	result.Nodes[result.NodeCount] = operator
	result.NodeCount++
	return result, true
}

func solveCompactStringBooleanAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if len(assertions) == 0 {
		return checkOutcome{}, false
	}
	formula, ok := assertions[0].(CompactStringBooleanFormula)
	if !ok {
		return checkOutcome{}, false
	}
	for _, assertion := range assertions[1:] {
		compact, compactOK := assertion.(CompactStringBooleanFormula)
		if !compactOK {
			return checkOutcome{}, false
		}
		formula, ok = CompactStringBooleanAndFormula(formula, compact)
		if !ok {
			return checkOutcome{}, false
		}
	}
	for assignment := 0; assignment < 1<<formula.AtomCount; assignment++ {
		if value, ok := evaluateCompactStringBooleanAssignment(formula, uint8(assignment)); !ok || !value {
			continue
		}
		var model stringModel
		consistent := true
		for index := 0; index < formula.AtomCount; index++ {
			if assignment&(1<<index) == 0 {
				continue
			}
			atom := formula.Atoms[index]
			if existing, found := model.lookup(atom.SymbolID); found && existing != atom.Literal {
				consistent = false
				break
			}
			model.set(atom.SymbolID, atom.Literal)
		}
		if !consistent {
			continue
		}
		for index := 0; index < formula.AtomCount; index++ {
			atom := formula.Atoms[index]
			if _, found := model.lookup(atom.SymbolID); found {
				continue
			}
			candidate := ""
			for conflictsCompactStringRegexLiteral(formula, assignment, atom.SymbolID, candidate) {
				candidate += "a"
			}
			model.set(atom.SymbolID, candidate)
		}
		if value, complete := evaluateCompactStringBooleanModel(formula, model); complete && value {
			return checkOutcome{status: checkSat, strings: model}, true
		}
	}
	return checkOutcome{status: checkUnsat}, true
}

func conflictsCompactStringRegexLiteral(formula CompactStringBooleanFormula, assignment int, symbolID int, candidate string) bool {
	for index := 0; index < formula.AtomCount; index++ {
		atom := formula.Atoms[index]
		if atom.SymbolID == symbolID && assignment&(1<<index) == 0 && atom.Literal == candidate {
			return true
		}
	}
	return false
}

func evaluateCompactStringBooleanAssignment(formula CompactStringBooleanFormula, assignment uint8) (bool, bool) {
	var stack [32]bool
	count := 0
	for index := 0; index < formula.NodeCount; index++ {
		node := formula.Nodes[index]
		switch {
		case node < uint8(formula.AtomCount):
			stack[count] = assignment&(1<<node) != 0
			count++
		case node == compactStringBooleanFalse || node == compactStringBooleanTrue:
			stack[count] = node == compactStringBooleanTrue
			count++
		case node == compactStringBooleanNot:
			if count < 1 {
				return false, false
			}
			stack[count-1] = !stack[count-1]
		case node == compactStringBooleanAnd || node == compactStringBooleanOr:
			if count < 2 {
				return false, false
			}
			right := stack[count-1]
			count--
			if node == compactStringBooleanAnd {
				stack[count-1] = stack[count-1] && right
			} else {
				stack[count-1] = stack[count-1] || right
			}
		default:
			return false, false
		}
	}
	return count == 1 && stack[0], count == 1
}

func evaluateCompactStringBooleanModel(formula CompactStringBooleanFormula, model stringModel) (bool, bool) {
	var assignment uint8
	for index := 0; index < formula.AtomCount; index++ {
		atom := formula.Atoms[index]
		value, ok := model.lookup(atom.SymbolID)
		if !ok {
			return false, false
		}
		if value == atom.Literal {
			assignment |= 1 << index
		}
	}
	return evaluateCompactStringBooleanAssignment(formula, assignment)
}

func CompactStringBooleanValue(model Model, formula CompactStringBooleanFormula) (bool, bool) {
	return evaluateCompactStringBooleanModel(formula, model.strings)
}
