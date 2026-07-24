package smt

// FloatingPointFromRealRelation constrains conversion of one exact Real symbol
// to a concrete target IEEE bit pattern. A symbol without an independent Real
// assignment may be synthesized when the target has a validated compact
// preimage.
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
	if relationCount == 0 {
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
	if realCount != 0 && !direct {
		var recognized bool
		outcome, recognized = solveLinearRealAssertions(realTerms[:realCount])
		if !recognized || outcome.status != checkSat {
			return outcome, recognized
		}
	}
	for relationIndex := 0; relationIndex < relationCount; relationIndex++ {
		relation := relations[relationIndex]
		if _, found := outcome.reals.lookup(relation.SymbolID); found {
			continue
		}
		synthesized := false
		for candidateIndex := 0; candidateIndex < relationCount; candidateIndex++ {
			candidateRelation := relations[candidateIndex]
			if candidateRelation.SymbolID != relation.SymbolID ||
				candidateRelation.Negated {
				continue
			}
			candidate, available, impossible :=
				synthesizeFloatingPointFromRealPreimage(candidateRelation)
			if impossible {
				return checkOutcome{status: checkUnsat}, true
			}
			if !available ||
				!floatingPointFromRealCandidateSatisfies(
					candidate, relations[:relationCount],
					relation.SymbolID,
				) {
				continue
			}
			outcome.reals.set(relation.SymbolID, candidate)
			synthesized = true
			break
		}
		if !synthesized {
			return checkOutcome{}, false
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

func synthesizeFloatingPointFromRealPreimage(
	relation FloatingPointFromRealRelation,
) (Rational, bool, bool) {
	target := FloatingPointFromBits(
		relation.ExponentBits, relation.SignificandBits, relation.Value,
	)
	if FloatingPointIsNaN(target) {
		return Rational{}, false, true
	}
	validate := func(candidate Rational) (Rational, bool, bool) {
		converted := floatingPointFromRational(
			relation.Mode, relation.ExponentBits,
			relation.SignificandBits, candidate,
		)
		if EqualBitVectorValue(FloatingPointBits(converted), relation.Value) {
			return candidate, true, false
		}
		return Rational{}, false, false
	}
	if finite, exact := floatingPointToRational(target); exact {
		if !FloatingPointIsZero(target) || !FloatingPointIsNegative(target) {
			return validate(finite)
		}
		if relation.Mode == 4 {
			return Rational{}, false, true
		}
		minimum, _ := floatingPointToRational(FloatingPointFromBits(
			relation.ExponentBits, relation.SignificandBits,
			NewBitVectorUint64(
				relation.ExponentBits+relation.SignificandBits, 1,
			),
		))
		return validate(NegateRational(DivideRational(
			minimum, NewRational(4, 1),
		)))
	}
	negative := FloatingPointIsNegative(target)
	if relation.Mode == 5 ||
		(!negative && relation.Mode == 4) ||
		(negative && relation.Mode == 3) {
		return Rational{}, false, true
	}
	positiveInfinity := FloatingPointPositiveInfinity(
		relation.ExponentBits, relation.SignificandBits,
	)
	maximumBits := SubBitVectorValue(
		FloatingPointBits(positiveInfinity),
		NewBitVectorUint64(
			relation.ExponentBits+relation.SignificandBits, 1,
		),
	)
	maximum, _ := floatingPointToRational(FloatingPointFromBits(
		relation.ExponentBits, relation.SignificandBits, maximumBits,
	))
	candidate := MultiplyRational(maximum, NewRational(2, 1))
	if negative {
		candidate = NegateRational(candidate)
	}
	return validate(candidate)
}

func floatingPointFromRealCandidateSatisfies(
	candidate Rational,
	relations []FloatingPointFromRealRelation,
	symbolID int,
) bool {
	for _, relation := range relations {
		if relation.SymbolID != symbolID {
			continue
		}
		converted := floatingPointFromRational(
			relation.Mode, relation.ExponentBits,
			relation.SignificandBits, candidate,
		)
		holds := EqualBitVectorValue(
			FloatingPointBits(converted), relation.Value,
		)
		if holds == relation.Negated {
			return false
		}
	}
	return true
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
