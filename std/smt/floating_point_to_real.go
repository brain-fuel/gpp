package smt

import (
	"math/big"
	"math/bits"
)

func floatingPointToRational(
	value FloatingPointValue,
) (Rational, bool) {
	if FloatingPointIsNaN(value) || FloatingPointIsInfinite(value) {
		return Rational{}, false
	}
	exponentBits := FloatingPointExponentBits(value)
	significandBits := FloatingPointSignificandBits(value)
	if exponentBits+significandBits <= 64 {
		if raw, inline := FloatingPointBits(value).Uint64(); inline {
			fractionBits := significandBits - 1
			fractionMask := uint64(1)<<fractionBits - 1
			magnitude := raw & fractionMask
			exponentMask := uint64(1)<<exponentBits - 1
			exponentField := raw >> fractionBits & exponentMask
			if exponentField == 0 && magnitude == 0 {
				return Rational{}, true
			}
			bias := int64(uint64(1)<<(exponentBits-1) - 1)
			unbiased := int64(1) - bias
			if exponentField != 0 {
				unbiased = int64(exponentField) - bias
				magnitude |= uint64(1) << fractionBits
			}
			scale := unbiased - int64(fractionBits)
			negative := raw>>(exponentBits+significandBits-1) != 0
			if scale >= 0 &&
				scale < 63 &&
				bits.Len64(magnitude)+int(scale) <= 63 {
				numerator := int64(magnitude << uint(scale))
				if negative {
					numerator = -numerator
				}
				return NewRational(numerator, 1), true
			}
			if scale < 0 && -scale < 63 && magnitude <= uint64(^uint64(0)>>1) {
				numerator := int64(magnitude)
				if negative {
					numerator = -numerator
				}
				return NewRational(numerator, int64(uint64(1)<<uint(-scale))), true
			}
		}
	}
	finite := decodeFloatingPointFinite(value)
	numerator := new(big.Int).Set(finite.magnitude)
	denominator := big.NewInt(1)
	if finite.scale.Sign() >= 0 {
		if !finite.scale.IsUint64() {
			panic("smt: floating-point exponent exceeds implementation limits")
		}
		numerator.Lsh(numerator, uint(finite.scale.Uint64()))
	} else {
		shift := new(big.Int).Neg(new(big.Int).Set(finite.scale))
		if !shift.IsUint64() {
			panic("smt: floating-point exponent exceeds implementation limits")
		}
		denominator.Lsh(denominator, uint(shift.Uint64()))
	}
	if finite.negative {
		numerator.Neg(numerator)
	}
	return rationalFromBig(new(big.Rat).SetFrac(numerator, denominator)), true
}
