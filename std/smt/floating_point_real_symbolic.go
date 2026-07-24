package smt

// FloatingPointFromRealRelation constrains conversion of one directly assigned
// exact Real symbol to a concrete target IEEE bit pattern.
type FloatingPointFromRealRelation struct {
	ExponentBits    int
	SignificandBits int
	SymbolID        int
	Mode            uint8
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointFromRealRelation) isTerm(BoolSort) {}

func NewFloatingPointFromRealRelation(
	exponentBits, significandBits, symbolID int,
	mode FloatingPointRoundingMode,
	value BitVectorValue,
) FloatingPointFromRealRelation {
	if exponentBits < 2 || significandBits < 2 || symbolID <= 0 {
		panic("smt: invalid real to floating-point relation")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: real to floating-point result width mismatch")
	}
	return FloatingPointFromRealRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		SymbolID: symbolID, Mode: floatingPointRoundingModeCode(mode),
		Value: value,
	}
}

func AssertFloatingPointFromRealRelation(
	assertion int,
	solver Solver,
	relation FloatingPointFromRealRelation,
) Solver {
	if assertion < 0 {
		panic("smt: negative assertion identity")
	}
	return solverValue{
		contextID: runtimeContextID(solver.contextID, assertion),
		depth:     solver.depth, state: solver.state.asserted(relation),
	}
}

func solveCompactRealToFloatingPointAssertions(
	assertions []Term[BoolSort],
) (checkOutcome, bool) {
	var realTerms [8]Term[BoolSort]
	var relations [4]FloatingPointFromRealRelation
	realCount, relationCount := 0, 0
	var appendTerm func(Term[BoolSort], bool) bool
	appendTerm = func(term Term[BoolSort], negated bool) bool {
		switch value := term.(type) {
		case And:
			if negated {
				return false
			}
			for _, item := range value.Values {
				if !appendTerm(item, false) {
					return false
				}
			}
			return true
		case BooleanConjunction:
			if negated {
				return false
			}
			items, polarities := value.values()
			for index, item := range items {
				if !appendTerm(item, polarities[index]) {
					return false
				}
			}
			return true
		case Not:
			return appendTerm(value.Value, !negated)
		case FloatingPointFromRealRelation:
			if relationCount == len(relations) {
				return false
			}
			value.Negated = value.Negated != negated
			relations[relationCount] = value
			relationCount++
			return true
		default:
			if negated || !containsRealTheory(term) ||
				realCount == len(realTerms) {
				return false
			}
			realTerms[realCount] = term
			realCount++
			return true
		}
	}
	for _, assertion := range assertions {
		if !appendTerm(assertion, false) {
			return checkOutcome{}, false
		}
	}
	if relationCount == 0 || realCount == 0 {
		return checkOutcome{}, false
	}
	outcome := checkOutcome{status: checkSat}
	direct := true
	for _, term := range realTerms[:realCount] {
		symbolID, value, ok := floatingPointDirectRealAssignment(term)
		if !ok {
			direct = false
			break
		}
		if previous, found := outcome.reals.lookup(symbolID); found &&
			CompareRational(previous, value) != 0 {
			return checkOutcome{status: checkUnsat}, true
		}
		outcome.reals.set(symbolID, value)
	}
	if !direct {
		var recognized bool
		outcome, recognized = solveLinearRealAssertions(realTerms[:realCount])
		if !recognized || outcome.status != checkSat {
			return outcome, recognized
		}
	}
	for _, relation := range relations[:relationCount] {
		value, found := outcome.reals.lookup(relation.SymbolID)
		if !found {
			return checkOutcome{}, false
		}
		converted := floatingPointFromRational(
			relation.Mode, relation.ExponentBits, relation.SignificandBits,
			value,
		)
		holds := EqualBitVectorValue(
			FloatingPointBits(converted), relation.Value,
		)
		if holds == relation.Negated {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	return outcome, true
}

func floatingPointDirectRealAssignment(
	term Term[BoolSort],
) (int, Rational, bool) {
	equality, ok := term.(Equal)
	if assignment, ok := term.(RealValueAssignment); ok {
		return assignment.ID, assignment.Value, true
	}
	if !ok {
		return 0, Rational{}, false
	}
	left, leftOK := equality.Left.(Term[RealSort])
	right, rightOK := equality.Right.(Term[RealSort])
	if !leftOK || !rightOK {
		return 0, Rational{}, false
	}
	if symbol, ok := left.(RealSymbol); ok {
		value, exact := ExactRealConstant(right)
		return symbol.ID, value, exact
	}
	if symbol, ok := right.(RealSymbol); ok {
		value, exact := ExactRealConstant(left)
		return symbol.ID, value, exact
	}
	return 0, Rational{}, false
}
