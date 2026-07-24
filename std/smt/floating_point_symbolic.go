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

const (
	FloatingPointComparisonLess uint8 = iota + 1
	FloatingPointComparisonLessOrEqual
)

const (
	FloatingPointOperationMin uint8 = iota + 1
	FloatingPointOperationMax
)

// FloatingPointBitVectorTermFromComponents implements SMT-LIB's native
// (fp sign exponent significand) constructor for arbitrary bit-vector terms.
func FloatingPointBitVectorTermFromComponents(
	exponentBits, significandBits int,
	sign, exponent, significand Term[BitVecSort],
) Term[BitVecSort] {
	if exponentBits < 2 {
		panic("smt: floating-point exponent width must be at least 2")
	}
	if significandBits < 2 {
		panic("smt: floating-point significand width must be at least 2")
	}
	return BitVecConcat(
		1, exponentBits+significandBits-1, sign,
		BitVecConcat(exponentBits, significandBits-1, exponent, significand),
	)
}

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

// FloatingPointComparisonRelation is the compact solver-neutral form of
// fp.lt/fp.leq between two same-format floating-point symbols.
type FloatingPointComparisonRelation struct {
	ExponentBits    int
	SignificandBits int
	LeftSymbolID    int
	RightSymbolID   int
	Comparison      uint8
	Negated         bool
}

func (FloatingPointComparisonRelation) isTerm(BoolSort) {}

// FloatingPointMinMaxRelation constrains the exact IEEE bits selected by
// fp.min/fp.max over two same-format symbols.
type FloatingPointMinMaxRelation struct {
	ExponentBits    int
	SignificandBits int
	LeftSymbolID    int
	RightSymbolID   int
	Operation       uint8
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointMinMaxRelation) isTerm(BoolSort) {}

type FloatingPointRoundToIntegralRelation struct {
	ExponentBits    int
	SignificandBits int
	SymbolID        int
	Mode            uint8
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointRoundToIntegralRelation) isTerm(BoolSort) {}

// FloatingPointAddRelation constrains the exact rounded IEEE bits of fp.add
// over two assigned same-format symbols.
type FloatingPointAddRelation struct {
	ExponentBits    int
	SignificandBits int
	LeftSymbolID    int
	RightSymbolID   int
	Mode            uint8
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointAddRelation) isTerm(BoolSort) {}

// FloatingPointSubRelation constrains the exact rounded IEEE bits of fp.sub
// over two assigned same-format symbols.
type FloatingPointSubRelation struct {
	ExponentBits    int
	SignificandBits int
	LeftSymbolID    int
	RightSymbolID   int
	Mode            uint8
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointSubRelation) isTerm(BoolSort) {}

// FloatingPointMulRelation constrains the exact rounded IEEE bits of fp.mul
// over two assigned same-format symbols.
type FloatingPointMulRelation struct {
	ExponentBits    int
	SignificandBits int
	LeftSymbolID    int
	RightSymbolID   int
	Mode            uint8
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointMulRelation) isTerm(BoolSort) {}

// FloatingPointDivRelation constrains the exact rounded IEEE bits of fp.div
// over two assigned same-format symbols.
type FloatingPointDivRelation struct {
	ExponentBits    int
	SignificandBits int
	LeftSymbolID    int
	RightSymbolID   int
	Mode            uint8
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointDivRelation) isTerm(BoolSort) {}

type floatingPointRoundToIntegralBitVector struct {
	exponentBits    int
	significandBits int
	value           Term[BitVecSort]
	mode            uint8
}

func (floatingPointRoundToIntegralBitVector) isTerm(BitVecSort) {}

func NewFloatingPointComparisonRelation(
	exponentBits, significandBits, leftSymbolID, rightSymbolID int,
	comparison uint8,
) FloatingPointComparisonRelation {
	if exponentBits < 2 {
		panic("smt: floating-point exponent width must be at least 2")
	}
	if significandBits < 2 {
		panic("smt: floating-point significand width must be at least 2")
	}
	if comparison < FloatingPointComparisonLess ||
		comparison > FloatingPointComparisonLessOrEqual {
		panic("smt: invalid floating-point comparison")
	}
	return FloatingPointComparisonRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		LeftSymbolID: leftSymbolID, RightSymbolID: rightSymbolID,
		Comparison: comparison,
	}
}

func NewFloatingPointMinMaxRelation(
	exponentBits, significandBits, leftSymbolID, rightSymbolID int,
	operation uint8,
	value BitVectorValue,
) FloatingPointMinMaxRelation {
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if operation < FloatingPointOperationMin || operation > FloatingPointOperationMax {
		panic("smt: invalid floating-point min/max operation")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: floating-point min/max result width mismatch")
	}
	return FloatingPointMinMaxRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		LeftSymbolID: leftSymbolID, RightSymbolID: rightSymbolID,
		Operation: operation, Value: value,
	}
}

func NewFloatingPointRoundToIntegralRelation(
	exponentBits, significandBits, symbolID int,
	mode FloatingPointRoundingMode,
	value BitVectorValue,
) FloatingPointRoundToIntegralRelation {
	modeCode := floatingPointRoundingModeCode(mode)
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: floating-point rounded result width mismatch")
	}
	return FloatingPointRoundToIntegralRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		SymbolID: symbolID, Mode: modeCode, Value: value,
	}
}

func NewFloatingPointAddRelation(
	exponentBits, significandBits, leftSymbolID, rightSymbolID int,
	mode FloatingPointRoundingMode,
	value BitVectorValue,
) FloatingPointAddRelation {
	modeCode := floatingPointRoundingModeCode(mode)
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: floating-point addition result width mismatch")
	}
	return FloatingPointAddRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		LeftSymbolID: leftSymbolID, RightSymbolID: rightSymbolID,
		Mode: modeCode, Value: value,
	}
}

func NewFloatingPointSubRelation(
	exponentBits, significandBits, leftSymbolID, rightSymbolID int,
	mode FloatingPointRoundingMode,
	value BitVectorValue,
) FloatingPointSubRelation {
	modeCode := floatingPointRoundingModeCode(mode)
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: floating-point subtraction result width mismatch")
	}
	return FloatingPointSubRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		LeftSymbolID: leftSymbolID, RightSymbolID: rightSymbolID,
		Mode: modeCode, Value: value,
	}
}

func NewFloatingPointMulRelation(
	exponentBits, significandBits, leftSymbolID, rightSymbolID int,
	mode FloatingPointRoundingMode,
	value BitVectorValue,
) FloatingPointMulRelation {
	modeCode := floatingPointRoundingModeCode(mode)
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: floating-point multiplication result width mismatch")
	}
	return FloatingPointMulRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		LeftSymbolID: leftSymbolID, RightSymbolID: rightSymbolID,
		Mode: modeCode, Value: value,
	}
}

func NewFloatingPointDivRelation(
	exponentBits, significandBits, leftSymbolID, rightSymbolID int,
	mode FloatingPointRoundingMode,
	value BitVectorValue,
) FloatingPointDivRelation {
	modeCode := floatingPointRoundingModeCode(mode)
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: floating-point division result width mismatch")
	}
	return FloatingPointDivRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		LeftSymbolID: leftSymbolID, RightSymbolID: rightSymbolID,
		Mode: modeCode, Value: value,
	}
}

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

// FloatingPointPredicateBitVectorTerm applies an SMT-LIB floating-point
// classification predicate to any exact IEEE bit-vector term.
func FloatingPointPredicateBitVectorTerm(
	exponentBits, significandBits int,
	value Term[BitVecSort],
	predicate uint8,
) Term[BoolSort] {
	if exponentBits < 2 {
		panic("smt: floating-point exponent width must be at least 2")
	}
	if significandBits < 2 {
		panic("smt: floating-point significand width must be at least 2")
	}
	if predicate < FloatingPointPredicateNaN ||
		predicate > FloatingPointPredicatePositive {
		panic("smt: invalid floating-point predicate")
	}
	total := exponentBits + significandBits
	exponent := BitVecExtract(total-2, significandBits-1, value)
	significand := BitVecExtract(significandBits-2, 0, value)
	exponentZero := Term[BoolSort](Equal{
		Left: exponent, Right: BitVecVal(exponentBits, 0),
	})
	exponentAll := Term[BoolSort](Equal{
		Left: exponent,
		Right: BitVectorTerm(
			NotBitVectorValue(NewBitVectorUint64(exponentBits, 0)),
		),
	})
	significandZero := Term[BoolSort](Equal{
		Left: significand, Right: BitVecVal(significandBits-1, 0),
	})
	sign := Term[BoolSort](Equal{
		Left:  BitVecExtract(total-1, total-1, value),
		Right: BitVecVal(1, 1),
	})
	nan := Term[BoolSort](And{Values: []Term[BoolSort]{
		exponentAll, Not{Value: significandZero},
	}})
	switch predicate {
	case FloatingPointPredicateNaN:
		return nan
	case FloatingPointPredicateInfinite:
		return And{Values: []Term[BoolSort]{exponentAll, significandZero}}
	case FloatingPointPredicateZero:
		return And{Values: []Term[BoolSort]{exponentZero, significandZero}}
	case FloatingPointPredicateSubnormal:
		return And{Values: []Term[BoolSort]{
			exponentZero, Not{Value: significandZero},
		}}
	case FloatingPointPredicateNormal:
		return And{Values: []Term[BoolSort]{
			Not{Value: exponentZero}, Not{Value: exponentAll},
		}}
	case FloatingPointPredicateNegative:
		return And{Values: []Term[BoolSort]{Not{Value: nan}, sign}}
	default:
		return And{Values: []Term[BoolSort]{
			Not{Value: nan}, Not{Value: sign},
		}}
	}
}

// FloatingPointEqualBitVectorTerms implements SMT-LIB fp.eq for arbitrary
// same-format IEEE bit-vector terms.
func FloatingPointEqualBitVectorTerms(
	exponentBits, significandBits int,
	left, right Term[BitVecSort],
) Term[BoolSort] {
	if exponentBits < 2 {
		panic("smt: floating-point exponent width must be at least 2")
	}
	if significandBits < 2 {
		panic("smt: floating-point significand width must be at least 2")
	}
	leftNaN := floatingPointNaNBitVectorTerm(
		exponentBits, significandBits, left,
	)
	rightNaN := floatingPointNaNBitVectorTerm(
		exponentBits, significandBits, right,
	)
	bothZero := And{Values: []Term[BoolSort]{
		floatingPointZeroBitVectorTerm(exponentBits, significandBits, left),
		floatingPointZeroBitVectorTerm(exponentBits, significandBits, right),
	}}
	return And{Values: []Term[BoolSort]{
		Not{Value: leftNaN},
		Not{Value: rightNaN},
		Or{Values: []Term[BoolSort]{
			Equal{Left: left, Right: right},
			bothZero,
		}},
	}}
}

// FloatingPointComparisonBitVectorTerms implements SMT-LIB fp.lt/fp.leq for
// arbitrary same-format IEEE bit-vector terms.
func FloatingPointComparisonBitVectorTerms(
	exponentBits, significandBits int,
	left, right Term[BitVecSort],
	comparison uint8,
) Term[BoolSort] {
	if comparison < FloatingPointComparisonLess ||
		comparison > FloatingPointComparisonLessOrEqual {
		panic("smt: invalid floating-point comparison")
	}
	less := floatingPointLessBitVectorTerm(
		exponentBits, significandBits, left, right,
	)
	if comparison == FloatingPointComparisonLess {
		return less
	}
	return Or{Values: []Term[BoolSort]{
		less,
		FloatingPointEqualBitVectorTerms(
			exponentBits, significandBits, left, right,
		),
	}}
}

// FloatingPointAbsBitVectorTerm clears the IEEE sign bit of an arbitrary
// floating-point bit-vector term.
func FloatingPointAbsBitVectorTerm(
	exponentBits, significandBits int,
	value Term[BitVecSort],
) Term[BitVecSort] {
	total := exponentBits + significandBits
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	return BitVecConcat(
		1, total-1, BitVecVal(1, 0),
		BitVecExtract(total-2, 0, value),
	)
}

// FloatingPointNegBitVectorTerm toggles the IEEE sign bit of an arbitrary
// floating-point bit-vector term.
func FloatingPointNegBitVectorTerm(
	exponentBits, significandBits int,
	value Term[BitVecSort],
) Term[BitVecSort] {
	total := exponentBits + significandBits
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	sign := BitVecConcat(
		1, total-1, BitVecVal(1, 1), BitVecVal(total-1, 0),
	)
	return BitVecXor(value, sign)
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

func AssertFloatingPointComparisonRelation(
	assertion int,
	solver Solver,
	relation FloatingPointComparisonRelation,
) Solver {
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

func AssertFloatingPointMinMaxRelation(
	assertion int,
	solver Solver,
	relation FloatingPointMinMaxRelation,
) Solver {
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

func AssertFloatingPointRoundToIntegralRelation(
	assertion int,
	solver Solver,
	relation FloatingPointRoundToIntegralRelation,
) Solver {
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

func AssertFloatingPointAddRelation(
	assertion int,
	solver Solver,
	relation FloatingPointAddRelation,
) Solver {
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

func AssertFloatingPointSubRelation(
	assertion int,
	solver Solver,
	relation FloatingPointSubRelation,
) Solver {
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

func AssertFloatingPointMulRelation(
	assertion int,
	solver Solver,
	relation FloatingPointMulRelation,
) Solver {
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

func AssertFloatingPointDivRelation(
	assertion int,
	solver Solver,
	relation FloatingPointDivRelation,
) Solver {
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

func FloatingPointRoundToIntegralBitVector(
	exponentBits, significandBits, symbolID int,
	symbolName string,
	mode FloatingPointRoundingMode,
) Term[BitVecSort] {
	total := exponentBits + significandBits
	return FloatingPointRoundToIntegralBitVectorTerm(
		exponentBits, significandBits,
		BitVecConst(total, symbolID, symbolName), mode,
	)
}

func FloatingPointRoundToIntegralBitVectorTerm(
	exponentBits, significandBits int,
	value Term[BitVecSort],
	mode FloatingPointRoundingMode,
) Term[BitVecSort] {
	modeCode := floatingPointRoundingModeCode(mode)
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point round-to-integral term")
	}
	return floatingPointRoundToIntegralBitVector{
		exponentBits: exponentBits, significandBits: significandBits,
		value: value, mode: modeCode,
	}
}

// FloatingPointMinMaxBitVector materializes the complete solver-neutral
// bit-vector selection term used outside the compact assigned-symbol path.
func FloatingPointMinMaxBitVector(
	exponentBits, significandBits, leftSymbolID, rightSymbolID int,
	leftName, rightName string,
	operation uint8,
) Term[BitVecSort] {
	total := exponentBits + significandBits
	left := BitVecConst(total, leftSymbolID, leftName)
	right := BitVecConst(total, rightSymbolID, rightName)
	return FloatingPointMinMaxBitVectorTerms(
		exponentBits, significandBits, left, right, operation,
	)
}

func FloatingPointMinMaxBitVectorTerms(
	exponentBits, significandBits int,
	left, right Term[BitVecSort],
	operation uint8,
) Term[BitVecSort] {
	leftNaN := floatingPointNaNBitVectorTerm(
		exponentBits, significandBits, left,
	)
	rightNaN := floatingPointNaNBitVectorTerm(
		exponentBits, significandBits, right,
	)
	less := floatingPointLessBitVectorTerm(
		exponentBits, significandBits, left, right,
	)
	numeric := Term[BitVecSort](If[BitVecSort]{
		Condition: less, Then: left, Else: right,
	})
	if operation == FloatingPointOperationMax {
		numeric = If[BitVecSort]{Condition: less, Then: right, Else: left}
	}
	return If[BitVecSort]{
		Condition: leftNaN,
		Then:      right,
		Else: If[BitVecSort]{
			Condition: rightNaN,
			Then:      left,
			Else:      numeric,
		},
	}
}

func floatingPointNaNBitVectorTerm(
	exponentBits, significandBits int,
	value Term[BitVecSort],
) Term[BoolSort] {
	total := exponentBits + significandBits
	exponent := BitVecExtract(total-2, significandBits-1, value)
	significand := BitVecExtract(significandBits-2, 0, value)
	return And{Values: []Term[BoolSort]{
		Equal{
			Left: exponent,
			Right: BitVectorTerm(
				NotBitVectorValue(NewBitVectorUint64(exponentBits, 0)),
			),
		},
		Not{Value: Equal{
			Left: significand, Right: BitVecVal(significandBits-1, 0),
		}},
	}}
}

func floatingPointZeroBitVectorTerm(
	exponentBits, significandBits int,
	value Term[BitVecSort],
) Term[BoolSort] {
	total := exponentBits + significandBits
	exponent := BitVecExtract(total-2, significandBits-1, value)
	significand := BitVecExtract(significandBits-2, 0, value)
	return And{Values: []Term[BoolSort]{
		Equal{Left: exponent, Right: BitVecVal(exponentBits, 0)},
		Equal{Left: significand, Right: BitVecVal(significandBits-1, 0)},
	}}
}

func floatingPointLessBitVectorTerm(
	exponentBits, significandBits int,
	left, right Term[BitVecSort],
) Term[BoolSort] {
	total := exponentBits + significandBits
	leftSign := Equal{
		Left: BitVecExtract(total-1, total-1, left), Right: BitVecVal(1, 1),
	}
	rightSign := Equal{
		Left: BitVecExtract(total-1, total-1, right), Right: BitVecVal(1, 1),
	}
	return And{Values: []Term[BoolSort]{
		Not{Value: floatingPointNaNBitVectorTerm(exponentBits, significandBits, left)},
		Not{Value: floatingPointNaNBitVectorTerm(exponentBits, significandBits, right)},
		Not{Value: And{Values: []Term[BoolSort]{
			floatingPointZeroBitVectorTerm(exponentBits, significandBits, left),
			floatingPointZeroBitVectorTerm(exponentBits, significandBits, right),
		}}},
		Or{Values: []Term[BoolSort]{
			And{Values: []Term[BoolSort]{leftSign, Not{Value: rightSign}}},
			And{Values: []Term[BoolSort]{leftSign, rightSign, BitVecULT(right, left)}},
			And{Values: []Term[BoolSort]{
				Not{Value: leftSign}, Not{Value: rightSign}, BitVecULT(left, right),
			}},
		}},
	}}
}

// FloatingPointSymbolModelBits returns the exact IEEE bit pattern assigned to
// a compact floating-point symbol.
func FloatingPointSymbolModelBits(model Model, symbolID int) (BitVectorValue, bool) {
	return model.bitVectors.lookup(symbolID)
}
