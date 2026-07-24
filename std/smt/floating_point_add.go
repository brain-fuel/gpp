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

func floatingPointSub(
	mode uint8,
	left, right FloatingPointValue,
) FloatingPointValue {
	if FloatingPointExponentBits(left) != FloatingPointExponentBits(right) ||
		FloatingPointSignificandBits(left) != FloatingPointSignificandBits(right) {
		panic("smt: floating-point subtraction format mismatch")
	}
	return floatingPointAdd(mode, left, FloatingPointNeg(right))
}

func floatingPointMul(
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
		panic("smt: floating-point multiplication format mismatch")
	}
	if FloatingPointIsNaN(left) || FloatingPointIsNaN(right) {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	total := exponentBits + significandBits
	leftNegative := FloatingPointBits(left).Bit(total - 1)
	rightNegative := FloatingPointBits(right).Bit(total - 1)
	negative := leftNegative != rightNegative
	leftInfinite, rightInfinite :=
		FloatingPointIsInfinite(left), FloatingPointIsInfinite(right)
	leftZero, rightZero := FloatingPointIsZero(left), FloatingPointIsZero(right)
	if leftInfinite || rightInfinite {
		if leftZero || rightZero {
			return FloatingPointNaN(exponentBits, significandBits)
		}
		if negative {
			return FloatingPointNegativeInfinity(exponentBits, significandBits)
		}
		return FloatingPointPositiveInfinity(exponentBits, significandBits)
	}
	if leftZero || rightZero {
		return floatingPointZero(exponentBits, significandBits, negative)
	}
	if significandBits <= 31 && total <= 64 {
		leftRaw, leftInline := FloatingPointBits(left).Uint64()
		rightRaw, rightInline := FloatingPointBits(right).Uint64()
		if leftInline && rightInline {
			return floatingPointMulUint64(
				mode, exponentBits, significandBits,
				leftRaw, rightRaw, negative,
			)
		}
	}
	leftFinite := decodeFloatingPointFinite(left)
	rightFinite := decodeFloatingPointFinite(right)
	product := new(big.Int).Mul(
		leftFinite.magnitude, rightFinite.magnitude,
	)
	scale := new(big.Int).Add(leftFinite.scale, rightFinite.scale)
	return floatingPointRoundExactBinary(
		mode, exponentBits, significandBits, negative, product, scale,
	)
}

func floatingPointMulUint64(
	mode uint8,
	exponentBits, significandBits int,
	leftRaw, rightRaw uint64,
	negative bool,
) FloatingPointValue {
	fractionBits := significandBits - 1
	exponentMask := uint64(1)<<exponentBits - 1
	fractionMask := uint64(1)<<fractionBits - 1
	bias := int64(uint64(1)<<(exponentBits-1) - 1)
	decode := func(raw uint64) (uint64, int64) {
		exponent := raw >> fractionBits & exponentMask
		fraction := raw & fractionMask
		if exponent == 0 {
			return fraction, 1 - bias - int64(fractionBits)
		}
		return fraction | uint64(1)<<fractionBits,
			int64(exponent) - bias - int64(fractionBits)
	}
	leftMagnitude, leftScale := decode(leftRaw)
	rightMagnitude, rightScale := decode(rightRaw)
	return floatingPointRoundExactBinaryUint64(
		mode, exponentBits, significandBits, negative,
		leftMagnitude*rightMagnitude, leftScale+rightScale,
	)
}

func floatingPointDiv(
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
		panic("smt: floating-point division format mismatch")
	}
	if FloatingPointIsNaN(left) || FloatingPointIsNaN(right) {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	total := exponentBits + significandBits
	negative := FloatingPointBits(left).Bit(total-1) !=
		FloatingPointBits(right).Bit(total-1)
	leftInfinite, rightInfinite :=
		FloatingPointIsInfinite(left), FloatingPointIsInfinite(right)
	leftZero, rightZero := FloatingPointIsZero(left), FloatingPointIsZero(right)
	if leftInfinite && rightInfinite || leftZero && rightZero {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	if leftInfinite || rightZero {
		if negative {
			return FloatingPointNegativeInfinity(exponentBits, significandBits)
		}
		return FloatingPointPositiveInfinity(exponentBits, significandBits)
	}
	if leftZero || rightInfinite {
		return floatingPointZero(exponentBits, significandBits, negative)
	}
	if significandBits <= 31 && total <= 64 {
		leftRaw, leftInline := FloatingPointBits(left).Uint64()
		rightRaw, rightInline := FloatingPointBits(right).Uint64()
		if leftInline && rightInline {
			return floatingPointDivUint64(
				mode, exponentBits, significandBits,
				leftRaw, rightRaw, negative,
			)
		}
	}
	leftFinite := decodeFloatingPointFinite(left)
	rightFinite := decodeFloatingPointFinite(right)
	scale := new(big.Int).Sub(leftFinite.scale, rightFinite.scale)
	return floatingPointRoundExactRational(
		mode, exponentBits, significandBits, negative,
		leftFinite.magnitude, rightFinite.magnitude, scale,
	)
}

func floatingPointFMA(
	mode uint8,
	left, right, addend FloatingPointValue,
) FloatingPointValue {
	if mode < 1 || mode > 5 {
		panic("smt: invalid floating-point rounding mode")
	}
	exponentBits := FloatingPointExponentBits(left)
	significandBits := FloatingPointSignificandBits(left)
	if exponentBits != FloatingPointExponentBits(right) ||
		significandBits != FloatingPointSignificandBits(right) ||
		exponentBits != FloatingPointExponentBits(addend) ||
		significandBits != FloatingPointSignificandBits(addend) {
		panic("smt: floating-point fused multiply-add format mismatch")
	}
	if FloatingPointIsNaN(left) || FloatingPointIsNaN(right) ||
		FloatingPointIsNaN(addend) {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	total := exponentBits + significandBits
	productNegative := FloatingPointBits(left).Bit(total-1) !=
		FloatingPointBits(right).Bit(total-1)
	addendNegative := FloatingPointBits(addend).Bit(total - 1)
	leftInfinite, rightInfinite :=
		FloatingPointIsInfinite(left), FloatingPointIsInfinite(right)
	leftZero, rightZero := FloatingPointIsZero(left), FloatingPointIsZero(right)
	addendInfinite := FloatingPointIsInfinite(addend)
	if (leftInfinite && rightZero) || (rightInfinite && leftZero) {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	if leftInfinite || rightInfinite {
		if addendInfinite && productNegative != addendNegative {
			return FloatingPointNaN(exponentBits, significandBits)
		}
		if productNegative {
			return FloatingPointNegativeInfinity(exponentBits, significandBits)
		}
		return FloatingPointPositiveInfinity(exponentBits, significandBits)
	}
	if addendInfinite {
		return addend
	}
	addendZero := FloatingPointIsZero(addend)
	if (leftZero || rightZero) && addendZero {
		negative := productNegative && addendNegative ||
			productNegative != addendNegative && mode == 4
		return floatingPointZero(exponentBits, significandBits, negative)
	}
	if leftZero || rightZero {
		return addend
	}
	if significandBits <= 31 && total <= 64 {
		leftRaw, leftInline := FloatingPointBits(left).Uint64()
		rightRaw, rightInline := FloatingPointBits(right).Uint64()
		addendRaw, addendInline := FloatingPointBits(addend).Uint64()
		if leftInline && rightInline && addendInline {
			if fused, ok := floatingPointFMAUint64(
				mode, exponentBits, significandBits,
				leftRaw, rightRaw, addendRaw,
				productNegative, addendNegative, addendZero,
			); ok {
				return fused
			}
		}
	}
	leftFinite := decodeFloatingPointFinite(left)
	rightFinite := decodeFloatingPointFinite(right)
	productMagnitude := new(big.Int).Mul(
		leftFinite.magnitude, rightFinite.magnitude,
	)
	productScale := new(big.Int).Add(leftFinite.scale, rightFinite.scale)
	if addendZero {
		return floatingPointRoundExactBinary(
			mode, exponentBits, significandBits, productNegative,
			productMagnitude, productScale,
		)
	}
	addendFinite := decodeFloatingPointFinite(addend)
	productTop := new(big.Int).Add(
		productScale, big.NewInt(int64(productMagnitude.BitLen()-1)),
	)
	addendTop := new(big.Int).Add(
		addendFinite.scale,
		big.NewInt(int64(addendFinite.magnitude.BitLen()-1)),
	)
	topDifference := new(big.Int).Sub(productTop, addendTop)
	if new(big.Int).Abs(new(big.Int).Set(topDifference)).Cmp(
		big.NewInt(int64(significandBits+4)),
	) > 0 {
		if topDifference.Sign() < 0 {
			direction := 1
			if productNegative {
				direction = -1
			}
			return floatingPointRoundNearRepresentable(
				mode, exponentBits, significandBits, addendFinite, direction,
			)
		}
		// The exact product is not necessarily representable. Append a
		// sufficiently remote sticky bit in the addend's numeric direction so
		// exact ties and directed modes see the perturbation without shifting
		// across an arbitrarily large exponent gap.
		stickyShift := uint(significandBits + 4)
		stickyMagnitude := new(big.Int).Lsh(
			new(big.Int).Set(productMagnitude), stickyShift,
		)
		if productNegative == addendNegative {
			stickyMagnitude.Add(stickyMagnitude, big.NewInt(1))
		} else {
			stickyMagnitude.Sub(stickyMagnitude, big.NewInt(1))
		}
		stickyScale := new(big.Int).Sub(
			productScale, big.NewInt(int64(stickyShift)),
		)
		return floatingPointRoundExactBinary(
			mode, exponentBits, significandBits, productNegative,
			stickyMagnitude, stickyScale,
		)
	}
	commonScale := productScale
	if addendFinite.scale.Cmp(commonScale) < 0 {
		commonScale = addendFinite.scale
	}
	productShift := new(big.Int).Sub(productScale, commonScale)
	addendShift := new(big.Int).Sub(addendFinite.scale, commonScale)
	if !productShift.IsInt64() || !addendShift.IsInt64() {
		panic("smt: floating-point fused multiply-add shift exceeds implementation limits")
	}
	productMagnitude.Lsh(productMagnitude, uint(productShift.Int64()))
	addendMagnitude := new(big.Int).Lsh(
		new(big.Int).Set(addendFinite.magnitude),
		uint(addendShift.Int64()),
	)
	if productNegative {
		productMagnitude.Neg(productMagnitude)
	}
	if addendNegative {
		addendMagnitude.Neg(addendMagnitude)
	}
	sum := new(big.Int).Add(productMagnitude, addendMagnitude)
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

func floatingPointSqrt(
	mode uint8,
	value FloatingPointValue,
) FloatingPointValue {
	if mode < 1 || mode > 5 {
		panic("smt: invalid floating-point rounding mode")
	}
	exponentBits := FloatingPointExponentBits(value)
	significandBits := FloatingPointSignificandBits(value)
	if FloatingPointIsNaN(value) {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	if FloatingPointIsZero(value) {
		return value
	}
	if FloatingPointIsNegative(value) {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	if FloatingPointIsInfinite(value) {
		return value
	}
	total := exponentBits + significandBits
	if significandBits <= 31 && total <= 64 {
		raw, inline := FloatingPointBits(value).Uint64()
		if inline {
			if root, ok := floatingPointSqrtUint64(
				mode, exponentBits, significandBits, raw,
			); ok {
				return root
			}
		}
	}
	finite := decodeFloatingPointFinite(value)
	return floatingPointRoundExactSqrt(
		mode, exponentBits, significandBits,
		finite.magnitude, finite.scale,
	)
}

func floatingPointRem(
	left, right FloatingPointValue,
) FloatingPointValue {
	exponentBits := FloatingPointExponentBits(left)
	significandBits := FloatingPointSignificandBits(left)
	if exponentBits != FloatingPointExponentBits(right) ||
		significandBits != FloatingPointSignificandBits(right) {
		panic("smt: floating-point remainder format mismatch")
	}
	if FloatingPointIsNaN(left) || FloatingPointIsNaN(right) ||
		FloatingPointIsInfinite(left) || FloatingPointIsZero(right) {
		return FloatingPointNaN(exponentBits, significandBits)
	}
	if FloatingPointIsZero(left) || FloatingPointIsInfinite(right) {
		return left
	}
	total := exponentBits + significandBits
	if significandBits <= 31 && total <= 64 {
		leftRaw, leftInline := FloatingPointBits(left).Uint64()
		rightRaw, rightInline := FloatingPointBits(right).Uint64()
		if leftInline && rightInline {
			if remainder, ok := floatingPointRemUint64(
				exponentBits, significandBits, leftRaw, rightRaw,
			); ok {
				return remainder
			}
		}
	}
	leftFinite := decodeFloatingPointFinite(left)
	rightFinite := decodeFloatingPointFinite(right)
	scaleDifference := new(big.Int).Sub(
		leftFinite.scale, rightFinite.scale,
	)
	var residual, residualScale *big.Int
	residualNegative := false
	if scaleDifference.Sign() >= 0 {
		modulus := new(big.Int).Lsh(
			new(big.Int).Set(rightFinite.magnitude), 1,
		)
		power := new(big.Int).Exp(
			big.NewInt(2), scaleDifference, modulus,
		)
		residue := new(big.Int).Mod(
			new(big.Int).Mul(leftFinite.magnitude, power), modulus,
		)
		quotientOdd := residue.Cmp(rightFinite.magnitude) >= 0
		residual = new(big.Int).Mod(
			new(big.Int).Set(residue), rightFinite.magnitude,
		)
		comparison := new(big.Int).Lsh(
			new(big.Int).Set(residual), 1,
		).Cmp(rightFinite.magnitude)
		increment := comparison > 0 ||
			comparison == 0 && quotientOdd
		if increment && residual.Sign() != 0 {
			residual.Sub(rightFinite.magnitude, residual)
			residualNegative = true
		}
		residualScale = rightFinite.scale
	} else {
		count := new(big.Int).Neg(scaleDifference)
		denominatorBits := new(big.Int).Add(
			big.NewInt(int64(rightFinite.magnitude.BitLen())), count,
		)
		if denominatorBits.Cmp(
			big.NewInt(int64(leftFinite.magnitude.BitLen()+1)),
		) > 0 {
			return left
		}
		if !count.IsInt64() {
			return left
		}
		denominator := new(big.Int).Lsh(
			new(big.Int).Set(rightFinite.magnitude), uint(count.Int64()),
		)
		quotient := new(big.Int)
		residual = new(big.Int)
		quotient.QuoRem(leftFinite.magnitude, denominator, residual)
		comparison := new(big.Int).Lsh(
			new(big.Int).Set(residual), 1,
		).Cmp(denominator)
		increment := comparison > 0 ||
			comparison == 0 && quotient.Bit(0) != 0
		if increment && residual.Sign() != 0 {
			residual.Sub(denominator, residual)
			residualNegative = true
		}
		residualScale = leftFinite.scale
	}
	if residual.Sign() == 0 {
		return floatingPointZero(
			exponentBits, significandBits, leftFinite.negative,
		)
	}
	return floatingPointRoundExactBinary(
		1, exponentBits, significandBits,
		leftFinite.negative != residualNegative,
		residual, residualScale,
	)
}

func floatingPointRemUint64(
	exponentBits, significandBits int,
	leftRaw, rightRaw uint64,
) (FloatingPointValue, bool) {
	fractionBits := significandBits - 1
	exponentMask := uint64(1)<<exponentBits - 1
	fractionMask := uint64(1)<<fractionBits - 1
	signBit := uint64(1) << (exponentBits + significandBits - 1)
	bias := int64(uint64(1)<<(exponentBits-1) - 1)
	decode := func(raw uint64) (uint64, int64) {
		exponent := raw >> fractionBits & exponentMask
		fraction := raw & fractionMask
		if exponent == 0 {
			return fraction, 1 - bias - int64(fractionBits)
		}
		return fraction | uint64(1)<<fractionBits,
			int64(exponent) - bias - int64(fractionBits)
	}
	leftMagnitude, leftScale := decode(leftRaw)
	rightMagnitude, rightScale := decode(rightRaw)
	difference := leftScale - rightScale
	numerator, denominator := leftMagnitude, rightMagnitude
	residualScale := leftScale
	if difference >= 0 {
		if difference >= 64 ||
			bits.Len64(leftMagnitude)+int(difference) > 64 {
			return FloatingPointValue{}, false
		}
		numerator <<= uint(difference)
		residualScale = rightScale
	} else {
		count := -difference
		if count >= 64 ||
			bits.Len64(rightMagnitude)+int(count) > 64 {
			return FloatingPointValue{}, false
		}
		denominator <<= uint(count)
	}
	quotient, residual := numerator/denominator, numerator%denominator
	increment := residual > denominator-residual ||
		residual == denominator-residual && quotient&1 != 0
	residualNegative := false
	if increment && residual != 0 {
		residual = denominator - residual
		residualNegative = true
	}
	leftNegative := leftRaw&signBit != 0
	if residual == 0 {
		return floatingPointZero(
			exponentBits, significandBits, leftNegative,
		), true
	}
	return floatingPointRoundExactBinaryUint64(
		1, exponentBits, significandBits,
		leftNegative != residualNegative,
		residual, residualScale,
	), true
}

func floatingPointSqrtUint64(
	mode uint8,
	exponentBits, significandBits int,
	raw uint64,
) (FloatingPointValue, bool) {
	fractionBits := significandBits - 1
	exponentMask := uint64(1)<<exponentBits - 1
	fractionMask := uint64(1)<<fractionBits - 1
	bias := int64(uint64(1)<<(exponentBits-1) - 1)
	exponent := raw >> fractionBits & exponentMask
	magnitude := raw & fractionMask
	scale := int64(1) - bias - int64(fractionBits)
	if exponent != 0 {
		magnitude |= uint64(1) << fractionBits
		scale = int64(exponent) - bias - int64(fractionBits)
	}
	logarithm := scale + int64(bits.Len64(magnitude)-1)
	topExponent := logarithm / 2
	if logarithm < 0 && logarithm&1 != 0 {
		topExponent--
	}
	minimumNormal := int64(1) - bias
	if topExponent < minimumNormal {
		return FloatingPointValue{}, false
	}
	quantum := topExponent - int64(fractionBits)
	power := scale - 2*quantum
	if power < 0 || power >= 64 ||
		bits.Len64(magnitude)+int(power) > 64 {
		return FloatingPointValue{}, false
	}
	radicand := magnitude << uint(power)
	units := floatingPointRoundedSqrtUint64(mode, radicand)
	if bits.Len64(units) > significandBits {
		units >>= 1
		topExponent++
	}
	exponentField := uint64(topExponent + bias)
	fraction := units & fractionMask
	return FloatingPointFromUint64(
		exponentBits, significandBits,
		exponentField<<fractionBits|fraction,
	), true
}

func floatingPointRoundedSqrtUint64(mode uint8, radicand uint64) uint64 {
	var low uint64
	high := uint64(1) << 32
	for high-low > 1 {
		middle := low + (high-low)/2
		if middle <= radicand/middle {
			low = middle
		} else {
			high = middle
		}
	}
	if low*low == radicand {
		return low
	}
	increment := mode == 3
	if mode == 1 || mode == 2 {
		midpoint := low<<1 | 1
		rightHigh, rightLow := bits.Mul64(midpoint, midpoint)
		leftHigh, leftLow := radicand>>62, radicand<<2
		comparison := 0
		if leftHigh < rightHigh ||
			leftHigh == rightHigh && leftLow < rightLow {
			comparison = -1
		} else if leftHigh > rightHigh ||
			leftHigh == rightHigh && leftLow > rightLow {
			comparison = 1
		}
		increment = comparison > 0 ||
			comparison == 0 && (mode == 2 || low&1 != 0)
	}
	if increment {
		low++
	}
	return low
}

func floatingPointFMAUint64(
	mode uint8,
	exponentBits, significandBits int,
	leftRaw, rightRaw, addendRaw uint64,
	productNegative, addendNegative, addendZero bool,
) (FloatingPointValue, bool) {
	fractionBits := significandBits - 1
	exponentMask := uint64(1)<<exponentBits - 1
	fractionMask := uint64(1)<<fractionBits - 1
	bias := int64(uint64(1)<<(exponentBits-1) - 1)
	decode := func(raw uint64) (uint64, int64) {
		exponent := raw >> fractionBits & exponentMask
		fraction := raw & fractionMask
		if exponent == 0 {
			return fraction, 1 - bias - int64(fractionBits)
		}
		return fraction | uint64(1)<<fractionBits,
			int64(exponent) - bias - int64(fractionBits)
	}
	leftMagnitude, leftScale := decode(leftRaw)
	rightMagnitude, rightScale := decode(rightRaw)
	productMagnitude := leftMagnitude * rightMagnitude
	productScale := leftScale + rightScale
	if addendZero {
		return floatingPointRoundExactBinaryUint64(
			mode, exponentBits, significandBits,
			productNegative, productMagnitude, productScale,
		), true
	}
	addendMagnitude, addendScale := decode(addendRaw)
	commonScale := productScale
	if addendScale < commonScale {
		commonScale = addendScale
	}
	productShift, addendShift :=
		productScale-commonScale, addendScale-commonScale
	if productShift >= 63 || addendShift >= 63 ||
		bits.Len64(productMagnitude)+int(productShift) > 63 ||
		bits.Len64(addendMagnitude)+int(addendShift) > 63 {
		return FloatingPointValue{}, false
	}
	productMagnitude <<= uint(productShift)
	addendMagnitude <<= uint(addendShift)
	var magnitude uint64
	negative := productNegative
	if productNegative == addendNegative {
		if productMagnitude > uint64(^uint64(0)>>1)-addendMagnitude {
			return FloatingPointValue{}, false
		}
		magnitude = productMagnitude + addendMagnitude
	} else if productMagnitude >= addendMagnitude {
		magnitude = productMagnitude - addendMagnitude
	} else {
		magnitude = addendMagnitude - productMagnitude
		negative = addendNegative
	}
	if magnitude == 0 {
		return floatingPointZero(
			exponentBits, significandBits, mode == 4,
		), true
	}
	return floatingPointRoundExactBinaryUint64(
		mode, exponentBits, significandBits,
		negative, magnitude, commonScale,
	), true
}

func floatingPointDivUint64(
	mode uint8,
	exponentBits, significandBits int,
	leftRaw, rightRaw uint64,
	negative bool,
) FloatingPointValue {
	fractionBits := significandBits - 1
	exponentMask := uint64(1)<<exponentBits - 1
	fractionMask := uint64(1)<<fractionBits - 1
	bias := int64(uint64(1)<<(exponentBits-1) - 1)
	decode := func(raw uint64) (uint64, int64) {
		exponent := raw >> fractionBits & exponentMask
		fraction := raw & fractionMask
		if exponent == 0 {
			return fraction, 1 - bias - int64(fractionBits)
		}
		return fraction | uint64(1)<<fractionBits,
			int64(exponent) - bias - int64(fractionBits)
	}
	numerator, leftScale := decode(leftRaw)
	denominator, rightScale := decode(rightRaw)
	return floatingPointRoundExactRationalUint64(
		mode, exponentBits, significandBits, negative,
		numerator, denominator, leftScale-rightScale,
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

// floatingPointRoundExactRational rounds
//
//	numerator / denominator * 2^scale
//
// directly from integers. It never passes through a host floating-point
// format, so arbitrary SMT-LIB formats retain exact tie and boundary behavior.
func floatingPointRoundExactRational(
	mode uint8,
	exponentBits, significandBits int,
	negative bool,
	numerator, denominator, scale *big.Int,
) FloatingPointValue {
	fractionBits := significandBits - 1
	bias := floatingPointBias(exponentBits)
	minimumNormal := new(big.Int).Sub(big.NewInt(1), bias)
	maximumNormal := new(big.Int).Set(bias)
	ratioExponent := numerator.BitLen() - denominator.BitLen()
	if compareRatioWithPowerOfTwo(numerator, denominator, ratioExponent) < 0 {
		ratioExponent--
	}
	topExponent := new(big.Int).Add(
		scale, big.NewInt(int64(ratioExponent)),
	)
	if topExponent.Cmp(minimumNormal) < 0 {
		quantum := new(big.Int).Sub(
			minimumNormal, big.NewInt(int64(fractionBits)),
		)
		power := new(big.Int).Sub(scale, quantum)
		units := floatingPointRoundedRatio(
			mode, negative, numerator, denominator, power,
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
	power := new(big.Int).Sub(scale, topExponent)
	power.Add(power, big.NewInt(int64(fractionBits)))
	significand := floatingPointRoundedRatio(
		mode, negative, numerator, denominator, power,
	)
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

func floatingPointRoundExactSqrt(
	mode uint8,
	exponentBits, significandBits int,
	magnitude, scale *big.Int,
) FloatingPointValue {
	fractionBits := significandBits - 1
	bias := floatingPointBias(exponentBits)
	minimumNormal := new(big.Int).Sub(big.NewInt(1), bias)
	maximumNormal := new(big.Int).Set(bias)
	logarithm := new(big.Int).Add(
		scale, big.NewInt(int64(magnitude.BitLen()-1)),
	)
	topExponent := new(big.Int).Rsh(logarithm, 1)
	quantum := new(big.Int).Sub(
		topExponent, big.NewInt(int64(fractionBits)),
	)
	subnormal := topExponent.Cmp(minimumNormal) < 0
	if subnormal {
		quantum.Sub(minimumNormal, big.NewInt(int64(fractionBits)))
	}
	units := floatingPointRoundedSqrt(
		mode, magnitude, scale, quantum, significandBits,
	)
	if units.Sign() == 0 {
		return floatingPointZero(exponentBits, significandBits, false)
	}
	if subnormal {
		if units.BitLen() >= significandBits {
			return floatingPointEncode(
				exponentBits, significandBits, false,
				big.NewInt(1), new(big.Int),
			)
		}
		return floatingPointEncode(
			exponentBits, significandBits, false,
			new(big.Int), units,
		)
	}
	if units.BitLen() > significandBits {
		units.Rsh(units, 1)
		topExponent.Add(topExponent, big.NewInt(1))
	}
	if topExponent.Cmp(maximumNormal) > 0 {
		return floatingPointOverflow(
			mode, exponentBits, significandBits, false,
		)
	}
	exponentField := new(big.Int).Add(topExponent, bias)
	units.SetBit(units, fractionBits, 0)
	return floatingPointEncode(
		exponentBits, significandBits, false, exponentField, units,
	)
}

func floatingPointRoundedSqrt(
	mode uint8,
	magnitude, scale, quantum *big.Int,
	significandBits int,
) *big.Int {
	power := new(big.Int).Sub(
		scale, new(big.Int).Lsh(new(big.Int).Set(quantum), 1),
	)
	var floor *big.Int
	var exact bool
	var midpointComparison int
	if power.Sign() >= 0 {
		if !power.IsInt64() {
			panic("smt: floating-point square-root shift exceeds implementation limits")
		}
		radicand := new(big.Int).Lsh(
			new(big.Int).Set(magnitude), uint(power.Int64()),
		)
		floor = new(big.Int).Sqrt(radicand)
		square := new(big.Int).Mul(
			new(big.Int).Set(floor), floor,
		)
		exact = square.Cmp(radicand) == 0
		midpoint := new(big.Int).Add(
			new(big.Int).Lsh(new(big.Int).Set(floor), 1),
			big.NewInt(1),
		)
		midpoint.Mul(midpoint, midpoint)
		midpointComparison = new(big.Int).Lsh(radicand, 2).Cmp(midpoint)
	} else {
		count := new(big.Int).Neg(power)
		upper := new(big.Int).Lsh(
			big.NewInt(1), uint(significandBits+1),
		)
		low, high := new(big.Int), upper
		one := big.NewInt(1)
		for new(big.Int).Sub(high, low).Cmp(one) > 0 {
			middle := new(big.Int).Rsh(
				new(big.Int).Add(low, high), 1,
			)
			square := new(big.Int).Mul(
				new(big.Int).Set(middle), middle,
			)
			if compareShiftedInteger(square, count, magnitude) <= 0 {
				low = middle
			} else {
				high = middle
			}
		}
		floor = low
		square := new(big.Int).Mul(new(big.Int).Set(floor), floor)
		exact = compareShiftedInteger(square, count, magnitude) == 0
		midpoint := new(big.Int).Add(
			new(big.Int).Lsh(new(big.Int).Set(floor), 1),
			big.NewInt(1),
		)
		midpoint.Mul(midpoint, midpoint)
		midpointComparison = -compareShiftedInteger(
			midpoint, count, new(big.Int).Lsh(new(big.Int).Set(magnitude), 2),
		)
	}
	if exact {
		return floor
	}
	increment := mode == 3
	if mode == 1 || mode == 2 {
		increment = midpointComparison > 0 ||
			midpointComparison == 0 && (mode == 2 || floor.Bit(0) != 0)
	}
	if increment {
		floor.Add(floor, big.NewInt(1))
	}
	return floor
}

func compareShiftedInteger(
	value, shift, target *big.Int,
) int {
	if value.Sign() == 0 {
		return -target.Sign()
	}
	shiftedBits := new(big.Int).Add(
		big.NewInt(int64(value.BitLen())), shift,
	)
	targetBits := big.NewInt(int64(target.BitLen()))
	if comparison := shiftedBits.Cmp(targetBits); comparison != 0 {
		return comparison
	}
	if !shift.IsInt64() {
		return 1
	}
	return new(big.Int).Lsh(
		new(big.Int).Set(value), uint(shift.Int64()),
	).Cmp(target)
}

func floatingPointRoundExactRationalUint64(
	mode uint8,
	exponentBits, significandBits int,
	negative bool,
	numerator, denominator uint64,
	scale int64,
) FloatingPointValue {
	fractionBits := significandBits - 1
	bias := int64(uint64(1)<<(exponentBits-1) - 1)
	minimumNormal, maximumNormal := int64(1)-bias, bias
	ratioExponent := bits.Len64(numerator) - bits.Len64(denominator)
	if compareRatioWithPowerOfTwoUint64(
		numerator, denominator, ratioExponent,
	) < 0 {
		ratioExponent--
	}
	topExponent := scale + int64(ratioExponent)
	if topExponent < minimumNormal {
		quantum := minimumNormal - int64(fractionBits)
		units := floatingPointRoundedRatioUint64(
			mode, negative, numerator, denominator, scale-quantum,
		)
		if units == 0 {
			return floatingPointZero(exponentBits, significandBits, negative)
		}
		if bits.Len64(units) >= significandBits {
			return FloatingPointFromUint64(
				exponentBits, significandBits, uint64(1)<<fractionBits,
			)
		}
		raw := units
		if negative {
			raw |= uint64(1) << (exponentBits + significandBits - 1)
		}
		return FloatingPointFromUint64(exponentBits, significandBits, raw)
	}
	significand := floatingPointRoundedRatioUint64(
		mode, negative, numerator, denominator,
		scale-topExponent+int64(fractionBits),
	)
	if bits.Len64(significand) > significandBits {
		significand >>= 1
		topExponent++
	}
	if topExponent > maximumNormal {
		return floatingPointOverflow(
			mode, exponentBits, significandBits, negative,
		)
	}
	exponentField := uint64(topExponent + bias)
	fraction := significand & (uint64(1)<<fractionBits - 1)
	raw := exponentField<<fractionBits | fraction
	if negative {
		raw |= uint64(1) << (exponentBits + significandBits - 1)
	}
	return FloatingPointFromUint64(exponentBits, significandBits, raw)
}

func compareRatioWithPowerOfTwoUint64(
	numerator, denominator uint64,
	exponent int,
) int {
	if exponent >= 0 {
		scaled := denominator << uint(exponent)
		if numerator < scaled {
			return -1
		}
		if numerator > scaled {
			return 1
		}
		return 0
	}
	scaled := numerator << uint(-exponent)
	if scaled < denominator {
		return -1
	}
	if scaled > denominator {
		return 1
	}
	return 0
}

func floatingPointRoundedRatioUint64(
	mode uint8,
	negative bool,
	numerator, denominator uint64,
	power int64,
) uint64 {
	var result, remainder uint64
	if power >= 0 {
		result, remainder = numerator/denominator, numerator%denominator
		if power > 63 {
			panic("smt: inline floating-point quotient shift exceeds limits")
		}
		for step := int64(0); step < power; step++ {
			remainder <<= 1
			result <<= 1
			if remainder >= denominator {
				remainder -= denominator
				result++
			}
		}
	} else {
		count := -power
		if count >= 63 ||
			denominator > ^uint64(0)>>uint(count) {
			result, remainder = 0, numerator
			if floatingPointDirectedIncrement(mode, negative) {
				return 1
			}
			return 0
		}
		scaledDenominator := denominator << uint(count)
		result, remainder = numerator/scaledDenominator,
			numerator%scaledDenominator
		denominator = scaledDenominator
	}
	if remainder == 0 {
		return result
	}
	increment := floatingPointDirectedIncrement(mode, negative)
	if mode == 1 || mode == 2 {
		comparison := -1
		if remainder > denominator-remainder {
			comparison = 1
		} else if remainder == denominator-remainder {
			comparison = 0
		}
		increment = comparison > 0 ||
			comparison == 0 && (mode == 2 || result&1 != 0)
	}
	if increment {
		result++
	}
	return result
}

func compareRatioWithPowerOfTwo(
	numerator, denominator *big.Int,
	exponent int,
) int {
	if exponent >= 0 {
		return numerator.Cmp(
			new(big.Int).Lsh(new(big.Int).Set(denominator), uint(exponent)),
		)
	}
	return new(big.Int).Lsh(
		new(big.Int).Set(numerator), uint(-exponent),
	).Cmp(denominator)
}

func floatingPointRoundedRatio(
	mode uint8,
	negative bool,
	numerator, denominator, power *big.Int,
) *big.Int {
	if !power.IsInt64() {
		if power.Sign() > 0 {
			panic("smt: floating-point quotient shift exceeds implementation limits")
		}
		result := new(big.Int)
		if floatingPointDirectedIncrement(mode, negative) {
			result.SetInt64(1)
		}
		return result
	}
	shift := power.Int64()
	scaledNumerator := new(big.Int).Set(numerator)
	scaledDenominator := new(big.Int).Set(denominator)
	if shift >= 0 {
		scaledNumerator.Lsh(scaledNumerator, uint(shift))
	} else {
		count := -shift
		if count > int64(numerator.BitLen()+2) {
			result := new(big.Int)
			if floatingPointDirectedIncrement(mode, negative) {
				result.SetInt64(1)
			}
			return result
		}
		scaledDenominator.Lsh(scaledDenominator, uint(count))
	}
	remainder := new(big.Int)
	result, _ := new(big.Int).QuoRem(
		scaledNumerator, scaledDenominator, remainder,
	)
	if remainder.Sign() == 0 {
		return result
	}
	increment := floatingPointDirectedIncrement(mode, negative)
	if mode == 1 || mode == 2 {
		comparison := new(big.Int).Lsh(remainder, 1).Cmp(scaledDenominator)
		increment = comparison > 0 ||
			comparison == 0 && (mode == 2 || result.Bit(0) != 0)
	}
	if increment {
		result.Add(result, big.NewInt(1))
	}
	return result
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
