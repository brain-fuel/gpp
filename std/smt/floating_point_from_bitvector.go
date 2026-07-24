package smt

import "math/big"

func floatingPointFromBitVector(
	mode uint8,
	exponentBits, significandBits int,
	value BitVectorValue,
	signed bool,
) FloatingPointValue {
	if mode < 1 || mode > 5 {
		panic("smt: invalid floating-point rounding mode")
	}
	if exponentBits < 2 || significandBits < 2 {
		panic("smt: invalid floating-point format")
	}
	if raw, inline := value.Uint64(); inline {
		negative := signed && value.Bit(value.Width()-1)
		magnitude := raw
		if negative {
			if value.Width() < 64 {
				magnitude &= uint64(1)<<value.Width() - 1
			}
			magnitude = -magnitude
			if value.Width() < 64 {
				magnitude &= uint64(1)<<value.Width() - 1
			}
		}
		if magnitude == 0 {
			return FloatingPointPositiveZero(exponentBits, significandBits)
		}
		return floatingPointRoundExactBinaryUint64(
			mode, exponentBits, significandBits,
			negative, magnitude, 0,
		)
	}
	integer := value.big()
	negative := signed && value.Bit(value.Width()-1)
	if negative {
		integer.Sub(
			integer,
			new(big.Int).Lsh(big.NewInt(1), uint(value.Width())),
		)
		integer.Neg(integer)
	}
	if integer.Sign() == 0 {
		return FloatingPointPositiveZero(exponentBits, significandBits)
	}
	return floatingPointRoundExactBinary(
		mode, exponentBits, significandBits,
		negative, integer, new(big.Int),
	)
}
