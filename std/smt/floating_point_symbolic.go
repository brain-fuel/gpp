package smt

const (
	FloatingPointPredicateNaN uint8 = iota + 1
	FloatingPointPredicateInfinite
	FloatingPointPredicateZero
	FloatingPointPredicateSubnormal
	FloatingPointPredicateNormal
	FloatingPointPredicateNegative
	FloatingPointPredicatePositive
)

// FloatingPointRelation is the compact solver-neutral form of a classification
// predicate over one IEEE/SMT-LIB floating-point bit-vector symbol.
type FloatingPointRelation struct {
	ExponentBits    int
	SignificandBits int
	SymbolID        int
	Predicate       uint8
	Negated         bool
}

func (FloatingPointRelation) isTerm(BoolSort) {}

func NewFloatingPointRelation(exponentBits, significandBits, symbolID int, predicate uint8) FloatingPointRelation {
	if exponentBits < 2 {
		panic("smt: floating-point exponent width must be at least 2")
	}
	if significandBits < 2 {
		panic("smt: floating-point significand width must be at least 2")
	}
	if predicate < FloatingPointPredicateNaN || predicate > FloatingPointPredicatePositive {
		panic("smt: invalid floating-point predicate")
	}
	return FloatingPointRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		SymbolID: symbolID, Predicate: predicate,
	}
}

func FloatingPointNaNRelation(exponentBits, significandBits, symbolID int) Term[BoolSort] {
	return NewFloatingPointRelation(exponentBits, significandBits, symbolID, FloatingPointPredicateNaN)
}

func FloatingPointInfiniteRelation(exponentBits, significandBits, symbolID int) Term[BoolSort] {
	return NewFloatingPointRelation(exponentBits, significandBits, symbolID, FloatingPointPredicateInfinite)
}

func FloatingPointZeroRelation(exponentBits, significandBits, symbolID int) Term[BoolSort] {
	return NewFloatingPointRelation(exponentBits, significandBits, symbolID, FloatingPointPredicateZero)
}

func FloatingPointSubnormalRelation(exponentBits, significandBits, symbolID int) Term[BoolSort] {
	return NewFloatingPointRelation(exponentBits, significandBits, symbolID, FloatingPointPredicateSubnormal)
}

func FloatingPointNormalRelation(exponentBits, significandBits, symbolID int) Term[BoolSort] {
	return NewFloatingPointRelation(exponentBits, significandBits, symbolID, FloatingPointPredicateNormal)
}

func FloatingPointNegativeRelation(exponentBits, significandBits, symbolID int) Term[BoolSort] {
	return NewFloatingPointRelation(exponentBits, significandBits, symbolID, FloatingPointPredicateNegative)
}

func FloatingPointPositiveRelation(exponentBits, significandBits, symbolID int) Term[BoolSort] {
	return NewFloatingPointRelation(exponentBits, significandBits, symbolID, FloatingPointPredicatePositive)
}

// AssertFloatingPointRelation preserves the concrete compact relation across
// the Go boundary instead of first boxing it through a general term builder.
func AssertFloatingPointRelation(assertion int, solver Solver, relation FloatingPointRelation) Solver {
	if assertion < 0 {
		panic("smt: negative assertion identity")
	}
	nextContext := runtimeContextID(solver.contextID, assertion)
	return solverValue{
		contextID: nextContext,
		depth:     solver.depth,
		state:     solver.state.asserted(relation),
	}
}

// FloatingPointSymbolModelBits returns the exact IEEE bit pattern assigned to
// a compact floating-point symbol.
func FloatingPointSymbolModelBits(model Model, symbolID int) (BitVectorValue, bool) {
	return model.bitVectors.lookup(symbolID)
}
