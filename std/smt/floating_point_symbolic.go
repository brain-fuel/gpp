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

// FloatingPointToBitVectorRelation constrains an indexed signed or unsigned
// conversion. An unconstrained FP source can use an integer-derived,
// forward-validated preimage when the result lies in the conversion image.
type FloatingPointToBitVectorRelation struct {
	ExponentBits    int
	SignificandBits int
	Width           int
	SymbolID        int
	Mode            uint8
	Signed          bool
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointToBitVectorRelation) isTerm(BoolSort) {}

// FloatingPointFromBitVectorRelation constrains an indexed signed or unsigned
// BV-to-FP conversion. An unconstrained BV source can use an integer-derived,
// forward-validated preimage when the result lies in the conversion image.
type FloatingPointFromBitVectorRelation struct {
	ExponentBits    int
	SignificandBits int
	Width           int
	SymbolID        int
	Mode            uint8
	Signed          bool
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointFromBitVectorRelation) isTerm(BoolSort) {}

// FloatingPointFormatConversionRelation constrains an exact rounded
// FP-to-FP conversion. An unconstrained source can use a reverse-converted,
// forward-validated target preimage when one exists.
type FloatingPointFormatConversionRelation struct {
	SourceExponentBits    int
	SourceSignificandBits int
	TargetExponentBits    int
	TargetSignificandBits int
	SymbolID              int
	Mode                  uint8
	Value                 BitVectorValue
	Negated               bool
}

func (FloatingPointFormatConversionRelation) isTerm(BoolSort) {}

// FloatingPointToRealRelation constrains exact affine combinations of finite
// fp.to_real values. A single-term equality can synthesize an unconstrained
// source when its rational target is exactly representable in the indexed
// format.
type FloatingPointToRealRelation struct {
	Count        int
	Terms        [4]FloatingPointToRealTerm
	Overflow     []FloatingPointToRealTerm
	RealCount    int
	RealTerms    [4]FloatingPointToRealRealTerm
	RealOverflow []FloatingPointToRealRealTerm
	Constant     Rational
	// Comparison is 0 for equality, 1 for <=, and 2 for <.
	Comparison uint8
	Negated    bool
	// Value remains the exact right-hand side for the direct-relation
	// constructor, preserving the established mutable compatibility surface.
	Value  Rational
	direct bool
}

func (FloatingPointToRealRelation) isTerm(BoolSort) {}

// FloatingPointToRealTerm is one exact affine coefficient applied to the
// finite rational value of an assigned floating-point symbol.
type FloatingPointToRealTerm struct {
	ExponentBits    int
	SignificandBits int
	SymbolID        int
	Coefficient     Rational
}

// FloatingPointToRealRealTerm is one ordinary Real symbol coefficient in a
// mixed FP-to-Real/LRA affine relation.
type FloatingPointToRealRealTerm struct {
	SymbolID    int
	Coefficient Rational
}

// FloatingPointAddRelation constrains the exact rounded IEEE bits of fp.add
// over two same-format symbols. Distinct unconstrained operands can use a
// validated result-plus-signed-zero canonical model.
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
// over two same-format symbols. Distinct unconstrained operands can use a
// validated result-minus-signed-zero canonical model.
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
// over two same-format symbols. Distinct unconstrained operands can use a
// validated result-times-one canonical model.
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
// over two same-format symbols. Distinct unconstrained operands can use a
// validated result-divided-by-one canonical model.
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

// FloatingPointFMARelation constrains the exact single-rounded IEEE bits of
// fp.fma over three same-format symbols. Distinct unconstrained operands can
// use a validated fma(result, one, signed-zero) canonical model.
type FloatingPointFMARelation struct {
	ExponentBits    int
	SignificandBits int
	LeftSymbolID    int
	RightSymbolID   int
	AddendSymbolID  int
	Mode            uint8
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointFMARelation) isTerm(BoolSort) {}

// FloatingPointSqrtRelation constrains the exact rounded IEEE bits of fp.sqrt.
// An unconstrained source can use an exact, validated target-square preimage.
type FloatingPointSqrtRelation struct {
	ExponentBits    int
	SignificandBits int
	SymbolID        int
	Mode            uint8
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointSqrtRelation) isTerm(BoolSort) {}

// FloatingPointRemRelation constrains the exact IEEE remainder bits over two
// same-format symbols. Distinct unconstrained operands can use the validated
// rem(result, positive-infinity) canonical model for finite results.
type FloatingPointRemRelation struct {
	ExponentBits    int
	SignificandBits int
	LeftSymbolID    int
	RightSymbolID   int
	Value           BitVectorValue
	Negated         bool
}

func (FloatingPointRemRelation) isTerm(BoolSort) {}

type floatingPointRoundToIntegralBitVector struct {
	exponentBits    int
	significandBits int
	value           Term[BitVecSort]
	mode            uint8
}

func (floatingPointRoundToIntegralBitVector) isTerm(BitVecSort) {}

type floatingPointToBitVectorTermValue struct {
	exponentBits    int
	significandBits int
	width           int
	value           Term[BitVecSort]
	mode            uint8
	signed          bool
}

func (floatingPointToBitVectorTermValue) isTerm(BitVecSort) {}

type floatingPointFromBitVectorTermValue struct {
	exponentBits    int
	significandBits int
	width           int
	value           Term[BitVecSort]
	mode            uint8
	signed          bool
}

func (floatingPointFromBitVectorTermValue) isTerm(BitVecSort) {}

type floatingPointFormatConversionTermValue struct {
	sourceExponentBits    int
	sourceSignificandBits int
	targetExponentBits    int
	targetSignificandBits int
	value                 Term[BitVecSort]
	mode                  uint8
}

func (floatingPointFormatConversionTermValue) isTerm(BitVecSort) {}

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

func NewFloatingPointToBitVectorRelation(
	exponentBits, significandBits, width, symbolID int,
	mode FloatingPointRoundingMode,
	signed bool,
	value BitVectorValue,
) FloatingPointToBitVectorRelation {
	if exponentBits < 2 || significandBits < 2 || width <= 0 {
		panic("smt: invalid floating-point conversion relation")
	}
	if value.Width() != width {
		panic("smt: floating-point conversion result width mismatch")
	}
	return FloatingPointToBitVectorRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		Width: width, SymbolID: symbolID,
		Mode: floatingPointRoundingModeCode(mode), Signed: signed,
		Value: value,
	}
}

func NewFloatingPointFromBitVectorRelation(
	exponentBits, significandBits, width, symbolID int,
	mode FloatingPointRoundingMode,
	signed bool,
	value BitVectorValue,
) FloatingPointFromBitVectorRelation {
	if exponentBits < 2 || significandBits < 2 || width <= 0 {
		panic("smt: invalid bit-vector to floating-point relation")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: bit-vector to floating-point result width mismatch")
	}
	return FloatingPointFromBitVectorRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		Width: width, SymbolID: symbolID,
		Mode: floatingPointRoundingModeCode(mode), Signed: signed,
		Value: value,
	}
}

func NewFloatingPointFormatConversionRelation(
	sourceExponentBits, sourceSignificandBits int,
	targetExponentBits, targetSignificandBits int,
	symbolID int,
	mode FloatingPointRoundingMode,
	value BitVectorValue,
) FloatingPointFormatConversionRelation {
	if sourceExponentBits < 2 || sourceSignificandBits < 2 ||
		targetExponentBits < 2 || targetSignificandBits < 2 {
		panic("smt: invalid floating-point format conversion relation")
	}
	if value.Width() != targetExponentBits+targetSignificandBits {
		panic("smt: floating-point format conversion result width mismatch")
	}
	return FloatingPointFormatConversionRelation{
		SourceExponentBits:    sourceExponentBits,
		SourceSignificandBits: sourceSignificandBits,
		TargetExponentBits:    targetExponentBits,
		TargetSignificandBits: targetSignificandBits,
		SymbolID:              symbolID, Mode: floatingPointRoundingModeCode(mode),
		Value: value,
	}
}

func NewFloatingPointToRealRelation(
	exponentBits, significandBits, symbolID int,
	value Rational,
) FloatingPointToRealRelation {
	relation := NewFloatingPointToRealInlineRelation(
		[4]FloatingPointToRealTerm{{
			ExponentBits: exponentBits, SignificandBits: significandBits,
			SymbolID: symbolID, Coefficient: NewRational(1, 1),
		}},
		1, NegateRational(value), 0,
	)
	relation.Value = value
	relation.direct = true
	return relation
}

// NewFloatingPointToRealAffineRelation constrains
//
//	sum(coefficient[i] * fp.to_real(symbol[i])) + constant
//
// by equality (comparison 0), non-strict upper bound (1), or strict upper
// bound (2). Symbols must have assigned IEEE bit patterns in the same compact
// conjunction.
func NewFloatingPointToRealAffineRelation(
	terms []FloatingPointToRealTerm,
	constant Rational,
	comparison uint8,
) FloatingPointToRealRelation {
	if len(terms) == 0 || comparison > 2 {
		panic("smt: invalid floating-point to Real affine relation")
	}
	relation := FloatingPointToRealRelation{
		Count: len(terms), Constant: constant, Comparison: comparison,
	}
	if len(terms) > len(relation.Terms) {
		relation.Overflow = make([]FloatingPointToRealTerm, len(terms))
	}
	for index, term := range terms {
		if term.ExponentBits < 2 || term.SignificandBits < 2 ||
			term.SymbolID <= 0 || term.Coefficient.Sign() == 0 {
			panic("smt: invalid floating-point to Real affine term")
		}
		if relation.Overflow != nil {
			relation.Overflow[index] = term
		} else {
			relation.Terms[index] = term
		}
	}
	return relation
}

// NewFloatingPointToRealInlineRelation is the allocation-free constructor for
// affine relations containing at most four converted symbols.
func NewFloatingPointToRealInlineRelation(
	terms [4]FloatingPointToRealTerm,
	count int,
	constant Rational,
	comparison uint8,
) FloatingPointToRealRelation {
	if count <= 0 || count > len(terms) || comparison > 2 {
		panic("smt: invalid inline floating-point to Real affine relation")
	}
	relation := FloatingPointToRealRelation{
		Count: count, Constant: constant, Comparison: comparison,
	}
	for index := 0; index < count; index++ {
		term := terms[index]
		if term.ExponentBits < 2 || term.SignificandBits < 2 ||
			term.SymbolID <= 0 || term.Coefficient.Sign() == 0 {
			panic("smt: invalid floating-point to Real affine term")
		}
		relation.Terms[index] = term
	}
	return relation
}

// NewMixedFloatingPointToRealInlineRelation constructs an allocation-free
// mixed relation with up to four converted floating-point symbols and four
// ordinary Real symbols.
func NewMixedFloatingPointToRealInlineRelation(
	floatingTerms [4]FloatingPointToRealTerm,
	floatingCount int,
	realTerms [4]FloatingPointToRealRealTerm,
	realCount int,
	constant Rational,
	comparison uint8,
) FloatingPointToRealRelation {
	relation := NewFloatingPointToRealInlineRelation(
		floatingTerms, floatingCount, constant, comparison,
	)
	if realCount <= 0 || realCount > len(realTerms) {
		panic("smt: invalid mixed floating-point to Real relation")
	}
	relation.RealCount = realCount
	for index := 0; index < realCount; index++ {
		term := realTerms[index]
		if term.SymbolID <= 0 || term.Coefficient.Sign() == 0 {
			panic("smt: invalid mixed floating-point Real term")
		}
		relation.RealTerms[index] = term
	}
	return relation
}

func (relation FloatingPointToRealRelation) values() []FloatingPointToRealTerm {
	if relation.Overflow != nil {
		return relation.Overflow[:relation.Count]
	}
	return relation.Terms[:relation.Count]
}

func (relation FloatingPointToRealRelation) realValues() []FloatingPointToRealRealTerm {
	if relation.RealOverflow != nil {
		return relation.RealOverflow[:relation.RealCount]
	}
	return relation.RealTerms[:relation.RealCount]
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

func NewFloatingPointFMARelation(
	exponentBits, significandBits int,
	leftSymbolID, rightSymbolID, addendSymbolID int,
	mode FloatingPointRoundingMode,
	value BitVectorValue,
) FloatingPointFMARelation {
	modeCode := floatingPointRoundingModeCode(mode)
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: floating-point fused multiply-add result width mismatch")
	}
	return FloatingPointFMARelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		LeftSymbolID: leftSymbolID, RightSymbolID: rightSymbolID,
		AddendSymbolID: addendSymbolID, Mode: modeCode, Value: value,
	}
}

func NewFloatingPointSqrtRelation(
	exponentBits, significandBits, symbolID int,
	mode FloatingPointRoundingMode,
	value BitVectorValue,
) FloatingPointSqrtRelation {
	modeCode := floatingPointRoundingModeCode(mode)
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: floating-point square-root result width mismatch")
	}
	return FloatingPointSqrtRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		SymbolID: symbolID, Mode: modeCode, Value: value,
	}
}

func NewFloatingPointRemRelation(
	exponentBits, significandBits, leftSymbolID, rightSymbolID int,
	value BitVectorValue,
) FloatingPointRemRelation {
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if value.Width() != exponentBits+significandBits {
		panic("smt: floating-point remainder result width mismatch")
	}
	return FloatingPointRemRelation{
		ExponentBits: exponentBits, SignificandBits: significandBits,
		LeftSymbolID: leftSymbolID, RightSymbolID: rightSymbolID,
		Value: value,
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

func AssertFloatingPointToBitVectorRelation(
	assertion int,
	solver Solver,
	relation FloatingPointToBitVectorRelation,
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

func AssertFloatingPointFromBitVectorRelation(
	assertion int,
	solver Solver,
	relation FloatingPointFromBitVectorRelation,
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

func AssertFloatingPointFormatConversionRelation(
	assertion int,
	solver Solver,
	relation FloatingPointFormatConversionRelation,
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

func AssertFloatingPointToRealRelation(
	assertion int,
	solver Solver,
	relation FloatingPointToRealRelation,
) Solver {
	if assertion < 0 {
		panic("smt: negative assertion identity")
	}
	return solverValue{
		contextID: runtimeContextID(solver.contextID, assertion),
		depth:     solver.depth, state: solver.state.asserted(relation),
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

func AssertFloatingPointFMARelation(
	assertion int,
	solver Solver,
	relation FloatingPointFMARelation,
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

func AssertFloatingPointSqrtRelation(
	assertion int,
	solver Solver,
	relation FloatingPointSqrtRelation,
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

func AssertFloatingPointRemRelation(
	assertion int,
	solver Solver,
	relation FloatingPointRemRelation,
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

func FloatingPointToUnsignedBitVectorTerm(
	exponentBits, significandBits, width int,
	value Term[BitVecSort],
	mode FloatingPointRoundingMode,
) Term[BitVecSort] {
	return floatingPointToBitVectorTerm(
		exponentBits, significandBits, width, value, mode, false,
	)
}

func FloatingPointToSignedBitVectorTerm(
	exponentBits, significandBits, width int,
	value Term[BitVecSort],
	mode FloatingPointRoundingMode,
) Term[BitVecSort] {
	return floatingPointToBitVectorTerm(
		exponentBits, significandBits, width, value, mode, true,
	)
}

func floatingPointToBitVectorTerm(
	exponentBits, significandBits, width int,
	value Term[BitVecSort],
	mode FloatingPointRoundingMode,
	signed bool,
) Term[BitVecSort] {
	if exponentBits < 2 || significandBits < 2 || width <= 0 {
		panic("smt: invalid floating-point to bit-vector term")
	}
	return floatingPointToBitVectorTermValue{
		exponentBits:    exponentBits,
		significandBits: significandBits,
		width:           width,
		value:           value,
		mode:            floatingPointRoundingModeCode(mode),
		signed:          signed,
	}
}

func FloatingPointFromUnsignedBitVectorTerm(
	exponentBits, significandBits, width int,
	value Term[BitVecSort],
	mode FloatingPointRoundingMode,
) Term[BitVecSort] {
	return floatingPointFromBitVectorTerm(
		exponentBits, significandBits, width, value, mode, false,
	)
}

func FloatingPointFromSignedBitVectorTerm(
	exponentBits, significandBits, width int,
	value Term[BitVecSort],
	mode FloatingPointRoundingMode,
) Term[BitVecSort] {
	return floatingPointFromBitVectorTerm(
		exponentBits, significandBits, width, value, mode, true,
	)
}

func floatingPointFromBitVectorTerm(
	exponentBits, significandBits, width int,
	value Term[BitVecSort],
	mode FloatingPointRoundingMode,
	signed bool,
) Term[BitVecSort] {
	if exponentBits < 2 || significandBits < 2 || width <= 0 {
		panic("smt: invalid bit-vector to floating-point term")
	}
	return floatingPointFromBitVectorTermValue{
		exponentBits:    exponentBits,
		significandBits: significandBits,
		width:           width, value: value,
		mode: floatingPointRoundingModeCode(mode), signed: signed,
	}
}

func FloatingPointFormatConversionTerm(
	sourceExponentBits, sourceSignificandBits int,
	targetExponentBits, targetSignificandBits int,
	value Term[BitVecSort],
	mode FloatingPointRoundingMode,
) Term[BitVecSort] {
	if sourceExponentBits < 2 || sourceSignificandBits < 2 ||
		targetExponentBits < 2 || targetSignificandBits < 2 {
		panic("smt: invalid floating-point format conversion term")
	}
	return floatingPointFormatConversionTermValue{
		sourceExponentBits:    sourceExponentBits,
		sourceSignificandBits: sourceSignificandBits,
		targetExponentBits:    targetExponentBits,
		targetSignificandBits: targetSignificandBits,
		value:                 value, mode: floatingPointRoundingModeCode(mode),
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
