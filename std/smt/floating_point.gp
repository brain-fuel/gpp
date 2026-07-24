package smt

// FloatingPointValue[e,s] is an exact SMT-LIB floating-point bit pattern.
// The exponent width e and significand width s (including the hidden bit) are
// retained as Go+ indices. The IEEE interchange encoding therefore has e+s
// bits: one sign bit, e exponent bits, and s-1 trailing significand bits.
//
// This is the ground-value foundation for floating-point support. It does not
// imply symbolic QF_FP arithmetic or rounding-mode support.
//goplus:derive off
//goplus:repr transparent
type FloatingPointValue[e nat, s nat] enum {
	floatingPointValue(ExponentBits int, SignificandBits int, Bits BitVectorValue) FloatingPointValue[e, s]
}

type FloatingPointRoundingMode enum {
	floatingPointRoundNearestTiesToEven
	floatingPointRoundNearestTiesToAway
	floatingPointRoundTowardPositive
	floatingPointRoundTowardNegative
	floatingPointRoundTowardZero
}

func RoundNearestTiesToEven() FloatingPointRoundingMode { return floatingPointRoundNearestTiesToEven }
func RoundNearestTiesToAway() FloatingPointRoundingMode { return floatingPointRoundNearestTiesToAway }
func RoundTowardPositive() FloatingPointRoundingMode { return floatingPointRoundTowardPositive }
func RoundTowardNegative() FloatingPointRoundingMode { return floatingPointRoundTowardNegative }
func RoundTowardZero() FloatingPointRoundingMode { return floatingPointRoundTowardZero }

func floatingPointRoundingModeCode(mode FloatingPointRoundingMode) uint8 {
	match mode {
	case floatingPointRoundNearestTiesToEven: return 1
	case floatingPointRoundNearestTiesToAway: return 2
	case floatingPointRoundTowardPositive: return 3
	case floatingPointRoundTowardNegative: return 4
	case floatingPointRoundTowardZero: return 5
	}
}

func FloatingPointFromBits(exponentBits nat, significandBits nat, bits BitVectorValue) FloatingPointValue[exponentBits, significandBits] {
	if exponentBits < 2 { panic("smt: floating-point exponent width must be at least 2") }
	if significandBits < 2 { panic("smt: floating-point significand width must be at least 2") }
	if bits.Width() != int(exponentBits+significandBits) { panic("smt: floating-point bit-pattern width mismatch") }
	return floatingPointValue(int(exponentBits), int(significandBits), bits)
}

func FloatingPointFromUint64(exponentBits nat, significandBits nat, bits uint64) FloatingPointValue[exponentBits, significandBits] {
	return FloatingPointFromBits(exponentBits, significandBits, NewBitVectorUint64(int(exponentBits+significandBits), bits))
}

func FloatingPointBits(0 e nat, 0 s nat, value FloatingPointValue[e, s]) BitVectorValue {
	match value { case floatingPointValue(_, _, bits): return bits }
}

func FloatingPointExponentBits(0 e nat, 0 s nat, value FloatingPointValue[e, s]) int {
	match value { case floatingPointValue(exponentBits, _, _): return exponentBits }
}

func FloatingPointSignificandBits(0 e nat, 0 s nat, value FloatingPointValue[e, s]) int {
	match value { case floatingPointValue(_, significandBits, _): return significandBits }
}

// FloatingPointAbs implements SMT-LIB fp.abs exactly at the IEEE encoding
// boundary: it clears only the sign bit, including for zeros, infinities, and
// NaNs.
func FloatingPointAbs(0 e nat, 0 s nat, value FloatingPointValue[e, s]) FloatingPointValue[e, s] {
	match value { case floatingPointValue(exponentBits, significandBits, bits):
		total := exponentBits+significandBits
		sign := ConcatBitVectorValue(NewBitVectorUint64(1, 1), NewBitVectorUint64(total-1, 0))
		return floatingPointValue(exponentBits, significandBits, AndBitVectorValue(bits, NotBitVectorValue(sign)))
	}
}

// FloatingPointNeg implements SMT-LIB fp.neg exactly at the IEEE encoding
// boundary by toggling only the sign bit.
func FloatingPointNeg(0 e nat, 0 s nat, value FloatingPointValue[e, s]) FloatingPointValue[e, s] {
	match value { case floatingPointValue(exponentBits, significandBits, bits):
		total := exponentBits+significandBits
		sign := ConcatBitVectorValue(NewBitVectorUint64(1, 1), NewBitVectorUint64(total-1, 0))
		return floatingPointValue(exponentBits, significandBits, XorBitVectorValue(bits, sign))
	}
}

func FloatingPointIsNegative(0 e nat, 0 s nat, value FloatingPointValue[e, s]) bool {
	match value { case floatingPointValue(exponentBits, significandBits, bits):
		return !FloatingPointIsNaN(value) && bits.Bit(exponentBits+significandBits-1)
	}
}

func FloatingPointIsPositive(0 e nat, 0 s nat, value FloatingPointValue[e, s]) bool {
	return !FloatingPointIsNaN(value) && !FloatingPointIsNegative(value)
}

func FloatingPointIsNaN(0 e nat, 0 s nat, value FloatingPointValue[e, s]) bool {
	match value { case floatingPointValue(exponentBits, significandBits, bits):
		return floatingPointExponentAll(bits, significandBits, exponentBits) &&
			floatingPointSignificandNonzero(bits, significandBits)
	}
}

func FloatingPointIsInfinite(0 e nat, 0 s nat, value FloatingPointValue[e, s]) bool {
	match value { case floatingPointValue(exponentBits, significandBits, bits):
		return floatingPointExponentAll(bits, significandBits, exponentBits) &&
			!floatingPointSignificandNonzero(bits, significandBits)
	}
}

func FloatingPointIsZero(0 e nat, 0 s nat, value FloatingPointValue[e, s]) bool {
	match value { case floatingPointValue(exponentBits, significandBits, bits):
		return floatingPointExponentNone(bits, significandBits, exponentBits) &&
			!floatingPointSignificandNonzero(bits, significandBits)
	}
}

func FloatingPointIsSubnormal(0 e nat, 0 s nat, value FloatingPointValue[e, s]) bool {
	match value { case floatingPointValue(exponentBits, significandBits, bits):
		return floatingPointExponentNone(bits, significandBits, exponentBits) &&
			floatingPointSignificandNonzero(bits, significandBits)
	}
}

func FloatingPointIsNormal(0 e nat, 0 s nat, value FloatingPointValue[e, s]) bool {
	match value { case floatingPointValue(exponentBits, significandBits, bits):
		return !floatingPointExponentNone(bits, significandBits, exponentBits) &&
			!floatingPointExponentAll(bits, significandBits, exponentBits)
	}
}

// FloatingPointEqual implements SMT-LIB fp.eq: NaNs compare false and the two
// signed zeros compare true; all other values compare by exact bit pattern.
func FloatingPointEqual(0 e nat, 0 s nat, left FloatingPointValue[e, s], right FloatingPointValue[e, s]) bool {
	if FloatingPointIsNaN(left) || FloatingPointIsNaN(right) { return false }
	if FloatingPointIsZero(left) && FloatingPointIsZero(right) { return true }
	return EqualBitVectorValue(FloatingPointBits(left), FloatingPointBits(right))
}

// FloatingPointLessThan implements SMT-LIB fp.lt. NaNs are unordered and the
// two signed zeros compare equal.
func FloatingPointLessThan(0 e nat, 0 s nat, left FloatingPointValue[e, s], right FloatingPointValue[e, s]) bool {
	if FloatingPointIsNaN(left) || FloatingPointIsNaN(right) { return false }
	if FloatingPointIsZero(left) && FloatingPointIsZero(right) { return false }
	leftNegative := FloatingPointBits(left).Bit(FloatingPointExponentBits(left)+FloatingPointSignificandBits(left)-1)
	rightNegative := FloatingPointBits(right).Bit(FloatingPointExponentBits(right)+FloatingPointSignificandBits(right)-1)
	if leftNegative != rightNegative { return leftNegative }
	comparison := CompareUnsignedBitVectorValue(FloatingPointBits(left), FloatingPointBits(right))
	if leftNegative { return comparison > 0 }
	return comparison < 0
}

func FloatingPointLessOrEqual(0 e nat, 0 s nat, left FloatingPointValue[e, s], right FloatingPointValue[e, s]) bool {
	return FloatingPointLessThan(left, right) || FloatingPointEqual(left, right)
}

func FloatingPointGreaterThan(0 e nat, 0 s nat, left FloatingPointValue[e, s], right FloatingPointValue[e, s]) bool {
	return FloatingPointLessThan(right, left)
}

func FloatingPointGreaterOrEqual(0 e nat, 0 s nat, left FloatingPointValue[e, s], right FloatingPointValue[e, s]) bool {
	return FloatingPointLessOrEqual(right, left)
}

// FloatingPointMin implements one deterministic result permitted by SMT-LIB
// fp.min: a sole NaN yields the numeric operand, two NaNs select the right
// payload, and equal signed zeros select the right operand.
func FloatingPointMin(0 e nat, 0 s nat, left FloatingPointValue[e, s], right FloatingPointValue[e, s]) FloatingPointValue[e, s] {
	if FloatingPointIsNaN(left) { return right }
	if FloatingPointIsNaN(right) { return left }
	if FloatingPointLessThan(left, right) { return left }
	return right
}

// FloatingPointMax is the corresponding deterministic SMT-LIB fp.max result.
// Equal signed zeros select the left operand.
func FloatingPointMax(0 e nat, 0 s nat, left FloatingPointValue[e, s], right FloatingPointValue[e, s]) FloatingPointValue[e, s] {
	if FloatingPointIsNaN(left) { return right }
	if FloatingPointIsNaN(right) { return left }
	if FloatingPointLessThan(left, right) { return right }
	return left
}

func FloatingPointRoundToIntegral(0 e nat, 0 s nat, mode FloatingPointRoundingMode, value FloatingPointValue[e, s]) FloatingPointValue[e, s] {
	return floatingPointRoundToIntegral(floatingPointRoundingModeCode(mode), value)
}

func floatingPointSignificandNonzero(bits BitVectorValue, significandBits int) bool {
	for index := 0; index < significandBits-1; index++ {
		if bits.Bit(index) { return true }
	}
	return false
}

func floatingPointExponentNone(bits BitVectorValue, significandBits int, exponentBits int) bool {
	for index := 0; index < exponentBits; index++ {
		if bits.Bit(significandBits-1+index) { return false }
	}
	return true
}

func floatingPointExponentAll(bits BitVectorValue, significandBits int, exponentBits int) bool {
	for index := 0; index < exponentBits; index++ {
		if !bits.Bit(significandBits-1+index) { return false }
	}
	return true
}
