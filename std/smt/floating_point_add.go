package smt

import "math/big"
import "math/bits"

type floatingPointFinite struct {
	negative  bool
	magnitude *big.Int
	scale     *big.Int
}

func floatingPointAdd(
	mode uint8,
	left, right FloatingPointValue,
) FloatingPointValue {
	if mode < 1 || mode > 5 {
		panic("smt: invalid floating-point rounding mode")
	}
	exponentBits := FloatingPointExponentBits(left)
	significandBits := FloatingPointSignificandBits(left)
	if exponentBits != FloatingPointExponentBits(right) ||
		significandBits != FloatingPointSignificandBits(right) {
		panic("smt: floating-point addition format mismatch")
	}
	if significandBits <= 29 && exponentBits+significandBits <= 64 {
		leftRaw, leftInline := FloatingPointBits(left).Uint64()
		rightRaw, rightInline := FloatingPointBits(right).Uint64()
		if leftInline && rightInline {
			return floatingPointAddUint64(
				mode, exponentBits, significandBits, leftRaw, rightRaw,
			)
		}
	}
	if FloatingPointIsNaN(left) || FloatingPointIsNaN(right) {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	leftInfinite, rightInfinite :=
		FloatingPointIsInfinite(left), FloatingPointIsInfinite(right)
	if leftInfinite || rightInfinite {
		if leftInfinite && rightInfinite &&
			FloatingPointIsNegative(left) != FloatingPointIsNegative(right) {
			return FloatingPointNaN(exponentBits, significandBits)
		}
		if leftInfinite {
			return left
		}
		return right
	}
	leftZero, rightZero := FloatingPointIsZero(left), FloatingPointIsZero(right)
	if leftZero && rightZero {
		leftNegative := FloatingPointBits(left).Bit(exponentBits + significandBits - 1)
		rightNegative := FloatingPointBits(right).Bit(exponentBits + significandBits - 1)
		negative := leftNegative && rightNegative ||
			leftNegative != rightNegative && mode == 4
		return floatingPointZero(exponentBits, significandBits, negative)
	}
	if leftZero {
		return right
	}
	if rightZero {
		return left
	}
	leftFinite := decodeFloatingPointFinite(left)
	rightFinite := decodeFloatingPointFinite(right)
	if dominant, direction, ok := floatingPointDominantAdd(
		significandBits, leftFinite, rightFinite,
	); ok {
		return floatingPointRoundNearRepresentable(
			mode, exponentBits, significandBits, dominant, direction,
		)
	}
	commonScale := leftFinite.scale
	if rightFinite.scale.Cmp(commonScale) < 0 {
		commonScale = rightFinite.scale
	}
	leftMagnitude := new(big.Int).Set(leftFinite.magnitude)
	rightMagnitude := new(big.Int).Set(rightFinite.magnitude)
	leftShift := new(big.Int).Sub(leftFinite.scale, commonScale)
	rightShift := new(big.Int).Sub(rightFinite.scale, commonScale)
	if leftShift.Sign() > 0 {
		leftMagnitude.Lsh(leftMagnitude, uint(leftShift.Int64()))
	}
	if rightShift.Sign() > 0 {
		rightMagnitude.Lsh(rightMagnitude, uint(rightShift.Int64()))
	}
	if leftFinite.negative {
		leftMagnitude.Neg(leftMagnitude)
	}
	if rightFinite.negative {
		rightMagnitude.Neg(rightMagnitude)
	}
	sum := new(big.Int).Add(leftMagnitude, rightMagnitude)
	if sum.Sign() == 0 {
		return floatingPointZero(
			exponentBits, significandBits, mode == 4,
		)
	}
	negative := sum.Sign() < 0
	sum.Abs(sum)
	return floatingPointRoundExactBinary(
		mode, exponentBits, significandBits, negative, sum, commonScale,
	)
}

type floatingPointFiniteUint64 struct {
	negative  bool
	magnitude uint64
	scale     int64
	raw       uint64
}

func floatingPointAddUint64(
	mode uint8,
	exponentBits, significandBits int,
	leftRaw, rightRaw uint64,
) FloatingPointValue {
	fractionBits := significandBits - 1
	exponentMask := uint64(1)<<exponentBits - 1
	fractionMask := uint64(1)<<fractionBits - 1
	signBit := uint64(1) << (exponentBits + significandBits - 1)
	leftExponent := leftRaw >> fractionBits & exponentMask
	rightExponent := rightRaw >> fractionBits & exponentMask
	leftFraction, rightFraction :=
		leftRaw&fractionMask, rightRaw&fractionMask
	leftNaN := leftExponent == exponentMask && leftFraction != 0
	rightNaN := rightExponent == exponentMask && rightFraction != 0
	if leftNaN || rightNaN {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	leftInfinite := leftExponent == exponentMask
	rightInfinite := rightExponent == exponentMask
	if leftInfinite || rightInfinite {
		if leftInfinite && rightInfinite &&
			leftRaw&signBit != rightRaw&signBit {
			return FloatingPointNaN(exponentBits, significandBits)
		}
		if leftInfinite {
			return FloatingPointFromUint64(exponentBits, significandBits, leftRaw)
		}
		return FloatingPointFromUint64(exponentBits, significandBits, rightRaw)
	}
	leftZero := leftExponent == 0 && leftFraction == 0
	rightZero := rightExponent == 0 && rightFraction == 0
	if leftZero && rightZero {
		leftNegative, rightNegative := leftRaw&signBit != 0, rightRaw&signBit != 0
		negative := leftNegative && rightNegative ||
			leftNegative != rightNegative && mode == 4
		return floatingPointZero(exponentBits, significandBits, negative)
	}
	if leftZero {
		return FloatingPointFromUint64(exponentBits, significandBits, rightRaw)
	}
	if rightZero {
		return FloatingPointFromUint64(exponentBits, significandBits, leftRaw)
	}
	bias := int64(uint64(1)<<(exponentBits-1) - 1)
	decode := func(raw, exponent, fraction uint64) floatingPointFiniteUint64 {
		unbiased := int64(exponent) - bias
		magnitude := fraction | uint64(1)<<fractionBits
		if exponent == 0 {
			unbiased = 1 - bias
			magnitude = fraction
		}
		return floatingPointFiniteUint64{
			negative:  raw&signBit != 0,
			magnitude: magnitude,
			scale:     unbiased - int64(fractionBits),
			raw:       raw,
		}
	}
	left := decode(leftRaw, leftExponent, leftFraction)
	right := decode(rightRaw, rightExponent, rightFraction)
	dominant, smaller := left, right
	if left.scale < right.scale {
		dominant, smaller = right, left
	}
	difference := dominant.scale - smaller.scale
	if difference > int64(significandBits+4) {
		direction := 1
		if smaller.negative {
			direction = -1
		}
		raw := dominant.raw
		switch mode {
		case 3:
			if direction > 0 {
				raw = floatingPointNextUpUint64(raw, signBit)
			}
		case 4:
			if direction < 0 {
				raw = floatingPointNextDownUint64(raw, signBit)
			}
		case 5:
			if !dominant.negative && direction < 0 {
				raw = floatingPointNextDownUint64(raw, signBit)
			}
			if dominant.negative && direction > 0 {
				raw = floatingPointNextUpUint64(raw, signBit)
			}
		}
		return FloatingPointFromUint64(exponentBits, significandBits, raw)
	}
	commonScale := left.scale
	if right.scale < commonScale {
		commonScale = right.scale
	}
	leftMagnitude := left.magnitude << uint(left.scale-commonScale)
	rightMagnitude := right.magnitude << uint(right.scale-commonScale)
	leftSigned, rightSigned := int64(leftMagnitude), int64(rightMagnitude)
	if left.negative {
		leftSigned = -leftSigned
	}
	if right.negative {
		rightSigned = -rightSigned
	}
	sum := leftSigned + rightSigned
	if sum == 0 {
		return floatingPointZero(exponentBits, significandBits, mode == 4)
	}
	negative := sum < 0
	magnitude := uint64(sum)
	if negative {
		magnitude = uint64(-sum)
	}
	return floatingPointRoundExactBinaryUint64(
		mode, exponentBits, significandBits,
		negative, magnitude, commonScale,
	)
}

func floatingPointRoundExactBinaryUint64(
	mode uint8,
	exponentBits, significandBits int,
	negative bool,
	magnitude uint64,
	scale int64,
) FloatingPointValue {
	fractionBits := significandBits - 1
	bias := int64(uint64(1)<<(exponentBits-1) - 1)
	minimumNormal, maximumNormal := int64(1)-bias, bias
	topExponent := scale + int64(bits.Len64(magnitude)-1)
	if topExponent < minimumNormal {
		quantum := minimumNormal - int64(fractionBits)
		units := floatingPointRoundedShiftUint64(
			mode, negative, magnitude, quantum-scale,
		)
		if units == 0 {
			return floatingPointZero(exponentBits, significandBits, negative)
		}
		if bits.Len64(units) >= significandBits {
			return FloatingPointFromUint64(
				exponentBits, significandBits,
				uint64(1)<<fractionBits,
			)
		}
		raw := units
		if negative {
			raw |= uint64(1) << (exponentBits + significandBits - 1)
		}
		return FloatingPointFromUint64(exponentBits, significandBits, raw)
	}
	shift := bits.Len64(magnitude) - significandBits
	significand := magnitude
	if shift > 0 {
		significand = floatingPointRoundedShiftUint64(
			mode, negative, magnitude, int64(shift),
		)
	} else {
		significand <<= uint(-shift)
	}
	if bits.Len64(significand) > significandBits {
		significand >>= 1
		topExponent++
	}
	if topExponent > maximumNormal {
		toInfinity := mode == 1 || mode == 2 ||
			mode == 3 && !negative || mode == 4 && negative
		if toInfinity {
			raw := (uint64(1)<<exponentBits - 1) << fractionBits
			if negative {
				raw |= uint64(1) << (exponentBits + significandBits - 1)
			}
			return FloatingPointFromUint64(exponentBits, significandBits, raw)
		}
		raw := (uint64(1)<<exponentBits-2)<<fractionBits |
			uint64(1)<<fractionBits - 1
		if negative {
			raw |= uint64(1) << (exponentBits + significandBits - 1)
		}
		return FloatingPointFromUint64(exponentBits, significandBits, raw)
	}
	exponentField := uint64(topExponent + bias)
	fraction := significand & (uint64(1)<<fractionBits - 1)
	raw := exponentField<<fractionBits | fraction
	if negative {
		raw |= uint64(1) << (exponentBits + significandBits - 1)
	}
	return FloatingPointFromUint64(exponentBits, significandBits, raw)
}

func floatingPointRoundedShiftUint64(
	mode uint8,
	negative bool,
	magnitude uint64,
	shift int64,
) uint64 {
	if shift <= 0 {
		return magnitude << uint(-shift)
	}
	if shift >= 64 {
		if floatingPointDirectedIncrement(mode, negative) {
			return 1
		}
		return 0
	}
	result := magnitude >> uint(shift)
	remainder := magnitude & (uint64(1)<<uint(shift) - 1)
	if remainder == 0 {
		return result
	}
	increment := floatingPointDirectedIncrement(mode, negative)
	if mode == 1 || mode == 2 {
		half := uint64(1) << uint(shift-1)
		increment = remainder > half ||
			remainder == half && (mode == 2 || result&1 != 0)
	}
	if increment {
		result++
	}
	return result
}

func floatingPointNextUpUint64(raw, signBit uint64) uint64 {
	if raw&signBit == 0 {
		return raw + 1
	}
	return raw - 1
}

func floatingPointNextDownUint64(raw, signBit uint64) uint64 {
	if raw&signBit == 0 {
		return raw - 1
	}
	return raw + 1
}

func decodeFloatingPointFinite(value FloatingPointValue) floatingPointFinite {
	exponentBits := FloatingPointExponentBits(value)
	significandBits := FloatingPointSignificandBits(value)
	fractionBits := significandBits - 1
	raw := FloatingPointBits(value).big()
	fractionMask := new(big.Int).Sub(
		new(big.Int).Lsh(big.NewInt(1), uint(fractionBits)),
		big.NewInt(1),
	)
	magnitude := new(big.Int).And(new(big.Int).Set(raw), fractionMask)
	exponentMask := new(big.Int).Sub(
		new(big.Int).Lsh(big.NewInt(1), uint(exponentBits)),
		big.NewInt(1),
	)
	exponentField := new(big.Int).And(
		new(big.Int).Rsh(new(big.Int).Set(raw), uint(fractionBits)),
		exponentMask,
	)
	bias := floatingPointBias(exponentBits)
	unbiased := new(big.Int)
	if exponentField.Sign() == 0 {
		unbiased.Sub(big.NewInt(1), bias)
	} else {
		unbiased.Sub(exponentField, bias)
		magnitude.SetBit(magnitude, fractionBits, 1)
	}
	scale := new(big.Int).Sub(unbiased, big.NewInt(int64(fractionBits)))
	return floatingPointFinite{
		negative:  raw.Bit(exponentBits+significandBits-1) != 0,
		magnitude: magnitude,
		scale:     scale,
	}
}

func floatingPointDominantAdd(
	significandBits int,
	left, right floatingPointFinite,
) (floatingPointFinite, int, bool) {
	leftScale, rightScale := left.scale, right.scale
	dominant, smaller := left, right
	if leftScale.Cmp(rightScale) < 0 {
		dominant, smaller = right, left
		leftScale, rightScale = rightScale, leftScale
	}
	difference := new(big.Int).Sub(leftScale, rightScale)
	if difference.Cmp(big.NewInt(int64(significandBits+4))) <= 0 {
		return floatingPointFinite{}, 0, false
	}
	direction := 1
	if smaller.negative {
		direction = -1
	}
	return dominant, direction, true
}

func floatingPointRoundNearRepresentable(
	mode uint8,
	exponentBits, significandBits int,
	dominant floatingPointFinite,
	direction int,
) FloatingPointValue {
	value := floatingPointEncodeFinite(
		exponentBits, significandBits, dominant,
	)
	switch mode {
	case 3:
		if direction > 0 {
			return floatingPointNextUp(value)
		}
	case 4:
		if direction < 0 {
			return floatingPointNextDown(value)
		}
	case 5:
		if !dominant.negative && direction < 0 {
			return floatingPointNextDown(value)
		}
		if dominant.negative && direction > 0 {
			return floatingPointNextUp(value)
		}
	}
	return value
}

func floatingPointRoundExactBinary(
	mode uint8,
	exponentBits, significandBits int,
	negative bool,
	magnitude, scale *big.Int,
) FloatingPointValue {
	fractionBits := significandBits - 1
	bias := floatingPointBias(exponentBits)
	minimumNormal := new(big.Int).Sub(big.NewInt(1), bias)
	maximumNormal := new(big.Int).Set(bias)
	topExponent := new(big.Int).Add(
		scale, big.NewInt(int64(magnitude.BitLen()-1)),
	)
	if topExponent.Cmp(minimumNormal) < 0 {
		quantum := new(big.Int).Sub(
			minimumNormal, big.NewInt(int64(fractionBits)),
		)
		shift := new(big.Int).Sub(quantum, scale)
		units := floatingPointRoundedShift(
			mode, negative, magnitude, shift,
		)
		if units.Sign() == 0 {
			return floatingPointZero(exponentBits, significandBits, negative)
		}
		if units.BitLen() >= significandBits {
			return floatingPointEncode(
				exponentBits, significandBits, negative,
				big.NewInt(1), new(big.Int),
			)
		}
		return floatingPointEncode(
			exponentBits, significandBits, negative,
			new(big.Int), units,
		)
	}
	shift := magnitude.BitLen() - significandBits
	significand := new(big.Int)
	if shift > 0 {
		significand = floatingPointRoundedShift(
			mode, negative, magnitude, big.NewInt(int64(shift)),
		)
	} else {
		significand.Lsh(new(big.Int).Set(magnitude), uint(-shift))
	}
	if significand.BitLen() > significandBits {
		significand.Rsh(significand, 1)
		topExponent.Add(topExponent, big.NewInt(1))
	}
	if topExponent.Cmp(maximumNormal) > 0 {
		return floatingPointOverflow(
			mode, exponentBits, significandBits, negative,
		)
	}
	exponentField := new(big.Int).Add(topExponent, bias)
	significand.SetBit(significand, fractionBits, 0)
	return floatingPointEncode(
		exponentBits, significandBits, negative,
		exponentField, significand,
	)
}

func floatingPointRoundedShift(
	mode uint8,
	negative bool,
	magnitude, shift *big.Int,
) *big.Int {
	if shift.Sign() <= 0 {
		if !shift.IsInt64() {
			panic("smt: floating-point shift exceeds implementation limits")
		}
		return new(big.Int).Lsh(
			new(big.Int).Set(magnitude), uint(-shift.Int64()),
		)
	}
	if !shift.IsInt64() || shift.Int64() > int64(magnitude.BitLen()+1) {
		result := new(big.Int)
		if floatingPointDirectedIncrement(mode, negative) {
			result.SetInt64(1)
		}
		return result
	}
	count := uint(shift.Int64())
	result := new(big.Int).Rsh(new(big.Int).Set(magnitude), count)
	remainderMask := new(big.Int).Sub(
		new(big.Int).Lsh(big.NewInt(1), count),
		big.NewInt(1),
	)
	remainder := new(big.Int).And(new(big.Int).Set(magnitude), remainderMask)
	if remainder.Sign() == 0 {
		return result
	}
	increment := floatingPointDirectedIncrement(mode, negative)
	if mode == 1 || mode == 2 {
		half := new(big.Int).Lsh(big.NewInt(1), count-1)
		comparison := remainder.Cmp(half)
		increment = comparison > 0 ||
			comparison == 0 && (mode == 2 || result.Bit(0) != 0)
	}
	if increment {
		result.Add(result, big.NewInt(1))
	}
	return result
}

func floatingPointDirectedIncrement(mode uint8, negative bool) bool {
	return mode == 3 && !negative || mode == 4 && negative
}

func floatingPointBias(exponentBits int) *big.Int {
	return new(big.Int).Sub(
		new(big.Int).Lsh(big.NewInt(1), uint(exponentBits-1)),
		big.NewInt(1),
	)
}

func floatingPointEncodeFinite(
	exponentBits, significandBits int,
	value floatingPointFinite,
) FloatingPointValue {
	return floatingPointRoundExactBinary(
		1, exponentBits, significandBits,
		value.negative, value.magnitude, value.scale,
	)
}

func floatingPointEncode(
	exponentBits, significandBits int,
	negative bool,
	exponentField, fraction *big.Int,
) FloatingPointValue {
	fractionBits := significandBits - 1
	raw := new(big.Int).Lsh(new(big.Int).Set(exponentField), uint(fractionBits))
	raw.Or(raw, fraction)
	if negative {
		raw.SetBit(raw, exponentBits+significandBits-1, 1)
	}
	return FloatingPointFromBits(
		exponentBits, significandBits,
		bitVectorValueFromBig(exponentBits+significandBits, raw),
	)
}

func floatingPointZero(
	exponentBits, significandBits int,
	negative bool,
) FloatingPointValue {
	if negative {
		return FloatingPointNegativeZero(exponentBits, significandBits)
	}
	return FloatingPointPositiveZero(exponentBits, significandBits)
}

func floatingPointOverflow(
	mode uint8,
	exponentBits, significandBits int,
	negative bool,
) FloatingPointValue {
	toInfinity := mode == 1 || mode == 2 ||
		mode == 3 && !negative || mode == 4 && negative
	if toInfinity {
		if negative {
			return FloatingPointNegativeInfinity(exponentBits, significandBits)
		}
		return FloatingPointPositiveInfinity(exponentBits, significandBits)
	}
	exponentField := new(big.Int).Sub(
		new(big.Int).Lsh(big.NewInt(1), uint(exponentBits)),
		big.NewInt(2),
	)
	fraction := new(big.Int).Sub(
		new(big.Int).Lsh(big.NewInt(1), uint(significandBits-1)),
		big.NewInt(1),
	)
	return floatingPointEncode(
		exponentBits, significandBits, negative, exponentField, fraction,
	)
}

func floatingPointNextUp(value FloatingPointValue) FloatingPointValue {
	exponentBits := FloatingPointExponentBits(value)
	significandBits := FloatingPointSignificandBits(value)
	raw := FloatingPointBits(value).big()
	sign := exponentBits + significandBits - 1
	if raw.Bit(sign) == 0 {
		raw.Add(raw, big.NewInt(1))
	} else {
		raw.Sub(raw, big.NewInt(1))
	}
	return FloatingPointFromBits(
		exponentBits, significandBits,
		bitVectorValueFromBig(exponentBits+significandBits, raw),
	)
}

func floatingPointNextDown(value FloatingPointValue) FloatingPointValue {
	exponentBits := FloatingPointExponentBits(value)
	significandBits := FloatingPointSignificandBits(value)
	raw := FloatingPointBits(value).big()
	sign := exponentBits + significandBits - 1
	if raw.Bit(sign) == 0 {
		raw.Sub(raw, big.NewInt(1))
	} else {
		raw.Add(raw, big.NewInt(1))
	}
	return FloatingPointFromBits(
		exponentBits, significandBits,
		bitVectorValueFromBig(exponentBits+significandBits, raw),
	)
}
