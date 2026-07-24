package smt

import (
	"math/big"
	"math/bits"
)

func floatingPointRoundToIntegral(
	mode uint8,
	value FloatingPointValue,
) FloatingPointValue {
	if mode < 1 || mode > 5 {
		panic("smt: invalid floating-point rounding mode")
	}
	exponentBits := FloatingPointExponentBits(value)
	significandBits := FloatingPointSignificandBits(value)
	if exponentBits+significandBits <= 64 {
		if raw, ok := FloatingPointBits(value).Uint64(); ok {
			return floatingPointRoundToIntegralUint64(
				mode, exponentBits, significandBits, raw,
			)
		}
	}
	if FloatingPointIsNaN(value) || FloatingPointIsInfinite(value) ||
		FloatingPointIsZero(value) {
		return value
	}
	fractionBits := significandBits - 1
	raw := FloatingPointBits(value).big()
	negative := raw.Bit(exponentBits+significandBits-1) != 0
	fractionMask := new(big.Int).Sub(
		new(big.Int).Lsh(big.NewInt(1), uint(fractionBits)),
		big.NewInt(1),
	)
	fraction := new(big.Int).And(new(big.Int).Set(raw), fractionMask)
	exponentMask := new(big.Int).Sub(
		new(big.Int).Lsh(big.NewInt(1), uint(exponentBits)),
		big.NewInt(1),
	)
	exponentField := new(big.Int).And(
		new(big.Int).Rsh(new(big.Int).Set(raw), uint(fractionBits)),
		exponentMask,
	)
	bias := new(big.Int).Sub(
		new(big.Int).Lsh(big.NewInt(1), uint(exponentBits-1)),
		big.NewInt(1),
	)
	effectiveExponent := new(big.Int).Sub(exponentField, bias)
	magnitude := new(big.Int).Set(fraction)
	if exponentField.Sign() == 0 {
		effectiveExponent = new(big.Int).Sub(big.NewInt(1), bias)
	} else {
		magnitude.SetBit(magnitude, fractionBits, 1)
	}
	shiftBig := new(big.Int).Sub(big.NewInt(int64(fractionBits)), effectiveExponent)
	if shiftBig.Sign() <= 0 {
		return value
	}
	var integer, remainder *big.Int
	shiftTooLarge := !shiftBig.IsInt64() ||
		shiftBig.Int64() > int64(magnitude.BitLen()+1)
	if shiftTooLarge {
		integer = new(big.Int)
		remainder = new(big.Int).Set(magnitude)
	} else {
		shift := uint(shiftBig.Int64())
		integer = new(big.Int).Rsh(new(big.Int).Set(magnitude), shift)
		mask := new(big.Int).Sub(
			new(big.Int).Lsh(big.NewInt(1), shift),
			big.NewInt(1),
		)
		remainder = new(big.Int).And(new(big.Int).Set(magnitude), mask)
	}
	increment := false
	if remainder.Sign() != 0 {
		switch mode {
		case 1, 2:
			twice := new(big.Int).Lsh(new(big.Int).Set(remainder), 1)
			comparison := -1
			if !shiftTooLarge {
				unit := new(big.Int).Lsh(
					big.NewInt(1), uint(shiftBig.Int64()),
				)
				comparison = twice.Cmp(unit)
			}
			increment = comparison > 0 ||
				comparison == 0 && (mode == 2 || integer.Bit(0) != 0)
		case 3:
			increment = !negative
		case 4:
			increment = negative
		}
	}
	if increment {
		integer.Add(integer, big.NewInt(1))
	}
	if integer.Sign() == 0 {
		bits := new(big.Int)
		if negative {
			bits.SetBit(bits, exponentBits+significandBits-1, 1)
		}
		return FloatingPointFromBits(
			exponentBits, significandBits,
			bitVectorValueFromBig(exponentBits+significandBits, bits),
		)
	}
	unbiased := integer.BitLen() - 1
	encodedExponent := new(big.Int).Add(big.NewInt(int64(unbiased)), bias)
	significand := new(big.Int).Set(integer)
	if unbiased > fractionBits {
		significand.Rsh(significand, uint(unbiased-fractionBits))
	} else {
		significand.Lsh(significand, uint(fractionBits-unbiased))
	}
	significand.SetBit(significand, fractionBits, 0)
	bits := new(big.Int).Lsh(encodedExponent, uint(fractionBits))
	bits.Or(bits, significand)
	if negative {
		bits.SetBit(bits, exponentBits+significandBits-1, 1)
	}
	return FloatingPointFromBits(
		exponentBits, significandBits,
		bitVectorValueFromBig(exponentBits+significandBits, bits),
	)
}

func floatingPointRoundToIntegralUint64(
	mode uint8,
	exponentBits, significandBits int,
	raw uint64,
) FloatingPointValue {
	fractionBits := significandBits - 1
	fractionMask := uint64(1)<<fractionBits - 1
	exponentMask := uint64(1)<<exponentBits - 1
	exponentField := raw >> fractionBits & exponentMask
	fraction := raw & fractionMask
	if exponentField == exponentMask || exponentField == 0 && fraction == 0 {
		return FloatingPointFromUint64(exponentBits, significandBits, raw)
	}
	negative := raw>>(exponentBits+significandBits-1) != 0
	bias := int64(uint64(1)<<(exponentBits-1) - 1)
	effectiveExponent := int64(exponentField) - bias
	magnitude := fraction
	if exponentField == 0 {
		effectiveExponent = 1 - bias
	} else {
		magnitude |= uint64(1) << fractionBits
	}
	if effectiveExponent >= int64(fractionBits) {
		return FloatingPointFromUint64(exponentBits, significandBits, raw)
	}
	shift := int64(fractionBits) - effectiveExponent
	var integer, remainder uint64
	if shift >= 64 {
		remainder = magnitude
	} else {
		integer = magnitude >> uint(shift)
		remainder = magnitude & (uint64(1)<<uint(shift) - 1)
	}
	increment := false
	if remainder != 0 {
		switch mode {
		case 1, 2:
			if shift < 64 {
				half := uint64(1) << uint(shift-1)
				increment = remainder > half ||
					remainder == half && (mode == 2 || integer&1 != 0)
			}
		case 3:
			increment = !negative
		case 4:
			increment = negative
		}
	}
	if increment {
		integer++
	}
	if integer == 0 {
		result := uint64(0)
		if negative {
			result = uint64(1) << (exponentBits + significandBits - 1)
		}
		return FloatingPointFromUint64(exponentBits, significandBits, result)
	}
	unbiased := bits.Len64(integer) - 1
	encodedExponent := uint64(int64(unbiased) + bias)
	significand := integer
	if unbiased > fractionBits {
		significand >>= uint(unbiased - fractionBits)
	} else {
		significand <<= uint(fractionBits - unbiased)
	}
	significand &^= uint64(1) << fractionBits
	result := encodedExponent<<fractionBits | significand
	if negative {
		result |= uint64(1) << (exponentBits + significandBits - 1)
	}
	return FloatingPointFromUint64(exponentBits, significandBits, result)
}
