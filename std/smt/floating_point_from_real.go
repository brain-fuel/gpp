package smt

import "math/big"

func floatingPointFromRational(
	mode uint8,
	exponentBits, significandBits int,
	value Rational,
) FloatingPointValue {
	if mode < 1 || mode > 5 {
		panic("smt: invalid floating-point rounding mode")
	}
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if numerator, denominator, small := value.small(); small &&
		exponentBits+significandBits <= 64 {
		if numerator == 0 {
			return FloatingPointPositiveZero(exponentBits, significandBits)
		}
		negative := numerator < 0
		magnitude := uint64(numerator)
		if negative {
			magnitude = uint64(-(numerator + 1))
			magnitude++
		}
		return floatingPointRoundExactRationalUint64(
			mode, exponentBits, significandBits,
			negative, magnitude, uint64(denominator), 0,
		)
	}
	rational := value.big()
	if rational.Sign() == 0 {
		return FloatingPointPositiveZero(exponentBits, significandBits)
	}
	negative := rational.Sign() < 0
	numerator := new(big.Int).Abs(new(big.Int).Set(rational.Num()))
	denominator := new(big.Int).Set(rational.Denom())
	return floatingPointRoundExactRational(
		mode, exponentBits, significandBits,
		negative, numerator, denominator, new(big.Int),
	)
}
