package smt

import (
	"fmt"
	"math/big"
	"math/bits"
)

// BitVectorValue is an exact unsigned bit pattern with an explicit positive
// width. Values are reduced modulo 2^width. Widths through 64 stay inline;
// larger values retain an arbitrary-precision representation.
type BitVectorValue struct {
	width int
	small uint64
	large *big.Int
}

func NewBitVectorUint64(width int, value uint64) BitVectorValue {
	if width <= 0 {
		panic("smt: bit-vector width must be positive")
	}
	if width < 64 {
		value &= uint64(1)<<width - 1
	}
	if width <= 64 {
		return BitVectorValue{width: width, small: value}
	}
	return BitVectorValue{width: width, large: new(big.Int).SetUint64(value)}
}

func ParseBitVector(width int, value string) (BitVectorValue, error) {
	if width <= 0 {
		return BitVectorValue{}, fmt.Errorf("bit-vector width must be positive")
	}
	parsed, ok := new(big.Int).SetString(value, 0)
	if !ok || parsed.Sign() < 0 {
		return BitVectorValue{}, fmt.Errorf("invalid unsigned bit-vector value %q", value)
	}
	modulus := new(big.Int).Lsh(big.NewInt(1), uint(width))
	parsed.Mod(parsed, modulus)
	if width <= 64 {
		return BitVectorValue{width: width, small: parsed.Uint64()}, nil
	}
	return BitVectorValue{width: width, large: parsed}, nil
}

func (value BitVectorValue) Width() int { return value.width }

func (value BitVectorValue) Bit(index int) bool {
	if index < 0 || index >= value.width {
		return false
	}
	if value.large != nil {
		return value.large.Bit(index) != 0
	}
	return value.small>>index&1 != 0
}

func (value BitVectorValue) Uint64() (uint64, bool) {
	return value.small, value.width <= 64
}

func EqualBitVectorValue(left, right BitVectorValue) bool {
	if left.width != right.width {
		return false
	}
	if left.large == nil && right.large == nil {
		return left.small == right.small
	}
	return left.big().Cmp(right.big()) == 0
}

func CompareUnsignedBitVectorValue(left, right BitVectorValue) int {
	if left.width != right.width {
		panic("smt: bit-vector width mismatch")
	}
	if left.large == nil && right.large == nil {
		if left.small < right.small {
			return -1
		}
		if left.small > right.small {
			return 1
		}
		return 0
	}
	return left.big().Cmp(right.big())
}

func CompareSignedBitVectorValue(left, right BitVectorValue) int {
	if left.width != right.width {
		panic("smt: bit-vector width mismatch")
	}
	leftNegative, rightNegative := left.Bit(left.width-1), right.Bit(right.width-1)
	if leftNegative != rightNegative {
		if leftNegative {
			return -1
		}
		return 1
	}
	return CompareUnsignedBitVectorValue(left, right)
}

func AndBitVectorValue(left, right BitVectorValue) BitVectorValue {
	if left.width != right.width {
		panic("smt: bit-vector width mismatch")
	}
	if left.large == nil && right.large == nil {
		return BitVectorValue{width: left.width, small: left.small & right.small}
	}
	return BitVectorValue{width: left.width, large: new(big.Int).And(left.big(), right.big())}
}

func OrBitVectorValue(left, right BitVectorValue) BitVectorValue {
	return binaryBitVectorValue(left, right, func(a, b *big.Int) *big.Int { return new(big.Int).Or(a, b) }, func(a, b uint64) uint64 { return a | b })
}
func XorBitVectorValue(left, right BitVectorValue) BitVectorValue {
	return binaryBitVectorValue(left, right, func(a, b *big.Int) *big.Int { return new(big.Int).Xor(a, b) }, func(a, b uint64) uint64 { return a ^ b })
}
func AddBitVectorValue(left, right BitVectorValue) BitVectorValue {
	return binaryBitVectorValue(left, right, func(a, b *big.Int) *big.Int { return new(big.Int).Add(a, b) }, func(a, b uint64) uint64 { return a + b })
}
func SubBitVectorValue(left, right BitVectorValue) BitVectorValue {
	return binaryBitVectorValue(left, right, func(a, b *big.Int) *big.Int { return new(big.Int).Sub(a, b) }, func(a, b uint64) uint64 { return a - b })
}
func MulBitVectorValue(left, right BitVectorValue) BitVectorValue {
	return binaryBitVectorValue(left, right, func(a, b *big.Int) *big.Int { return new(big.Int).Mul(a, b) }, func(a, b uint64) uint64 { return a * b })
}

func ShiftLeftBitVectorValue(value, amount BitVectorValue) BitVectorValue {
	shift := bitVectorShiftAmount(amount, value.width)
	if shift >= value.width {
		return NewBitVectorUint64(value.width, 0)
	}
	if value.width <= 64 {
		return NewBitVectorUint64(value.width, value.small<<shift)
	}
	result := new(big.Int).Lsh(value.big(), uint(shift))
	result.Mod(result, new(big.Int).Lsh(big.NewInt(1), uint(value.width)))
	return BitVectorValue{width: value.width, large: result}
}

func LogicalShiftRightBitVectorValue(value, amount BitVectorValue) BitVectorValue {
	shift := bitVectorShiftAmount(amount, value.width)
	if shift >= value.width {
		return NewBitVectorUint64(value.width, 0)
	}
	if value.width <= 64 {
		return NewBitVectorUint64(value.width, value.small>>shift)
	}
	return BitVectorValue{width: value.width, large: new(big.Int).Rsh(value.big(), uint(shift))}
}

func ArithmeticShiftRightBitVectorValue(value, amount BitVectorValue) BitVectorValue {
	shift := bitVectorShiftAmount(amount, value.width)
	negative := value.Bit(value.width - 1)
	if shift >= value.width {
		if !negative {
			return NewBitVectorUint64(value.width, 0)
		}
		return NotBitVectorValue(NewBitVectorUint64(value.width, 0))
	}
	if value.width <= 64 {
		if !negative {
			return NewBitVectorUint64(value.width, value.small>>shift)
		}
		fill := ^uint64(0) << (value.width - shift)
		return NewBitVectorUint64(value.width, value.small>>shift|fill)
	}
	signed := value.big()
	if negative {
		signed.Sub(signed, new(big.Int).Lsh(big.NewInt(1), uint(value.width)))
	}
	signed.Rsh(signed, uint(shift))
	if signed.Sign() < 0 {
		signed.Add(signed, new(big.Int).Lsh(big.NewInt(1), uint(value.width)))
	}
	return BitVectorValue{width: value.width, large: signed}
}

func bitVectorShiftAmount(amount BitVectorValue, width int) int {
	if amount.width != width {
		panic("smt: bit-vector width mismatch")
	}
	if amount.large != nil {
		if !amount.large.IsInt64() || amount.large.Int64() >= int64(width) {
			return width
		}
		return int(amount.large.Int64())
	}
	if amount.small >= uint64(width) {
		return width
	}
	return int(amount.small)
}

func UnsignedDivBitVectorValue(left, right BitVectorValue) BitVectorValue {
	if left.width != right.width {
		panic("smt: bit-vector width mismatch")
	}
	if left.width <= 64 {
		if right.small == 0 {
			return NotBitVectorValue(NewBitVectorUint64(left.width, 0))
		}
		return NewBitVectorUint64(left.width, left.small/right.small)
	}
	if right.big().Sign() == 0 {
		return NotBitVectorValue(NewBitVectorUint64(left.width, 0))
	}
	return bitVectorValueFromBig(left.width, new(big.Int).Quo(left.big(), right.big()))
}

func UnsignedRemBitVectorValue(left, right BitVectorValue) BitVectorValue {
	if left.width != right.width {
		panic("smt: bit-vector width mismatch")
	}
	if left.width <= 64 {
		if right.small == 0 {
			return left
		}
		return NewBitVectorUint64(left.width, left.small%right.small)
	}
	if right.big().Sign() == 0 {
		return left
	}
	return bitVectorValueFromBig(left.width, new(big.Int).Rem(left.big(), right.big()))
}

func SignedDivBitVectorValue(left, right BitVectorValue) BitVectorValue {
	if left.width != right.width {
		panic("smt: bit-vector width mismatch")
	}
	leftSigned, rightSigned := left.signedBig(), right.signedBig()
	if rightSigned.Sign() == 0 {
		if leftSigned.Sign() < 0 {
			return NewBitVectorUint64(left.width, 1)
		}
		return NotBitVectorValue(NewBitVectorUint64(left.width, 0))
	}
	return bitVectorValueFromBig(left.width, new(big.Int).Quo(leftSigned, rightSigned))
}

func SignedRemBitVectorValue(left, right BitVectorValue) BitVectorValue {
	if left.width != right.width {
		panic("smt: bit-vector width mismatch")
	}
	rightSigned := right.signedBig()
	if rightSigned.Sign() == 0 {
		return left
	}
	return bitVectorValueFromBig(left.width, new(big.Int).Rem(left.signedBig(), rightSigned))
}

func (value BitVectorValue) signedBig() *big.Int {
	result := value.big()
	if value.Bit(value.width - 1) {
		result.Sub(result, new(big.Int).Lsh(big.NewInt(1), uint(value.width)))
	}
	return result
}

func bitVectorValueFromBig(width int, value *big.Int) BitVectorValue {
	modulus := new(big.Int).Lsh(big.NewInt(1), uint(width))
	value.Mod(value, modulus)
	if width <= 64 {
		return NewBitVectorUint64(width, value.Uint64())
	}
	return BitVectorValue{width: width, large: value}
}

func ConcatBitVectorValue(first, second BitVectorValue) BitVectorValue {
	if first.width+second.width <= 64 {
		return NewBitVectorUint64(first.width+second.width, first.small<<second.width|second.small)
	}
	result := new(big.Int).Lsh(first.big(), uint(second.width))
	result.Or(result, second.big())
	return bitVectorValueFromBig(first.width+second.width, result)
}

func ExtractBitVectorValue(value BitVectorValue, high, low int) BitVectorValue {
	if low < 0 || high < low || high >= value.width {
		panic("smt: invalid bit-vector extraction range")
	}
	if value.width <= 64 {
		return NewBitVectorUint64(high-low+1, value.small>>low)
	}
	result := new(big.Int).Rsh(value.big(), uint(low))
	return bitVectorValueFromBig(high-low+1, result)
}

func ZeroExtendBitVectorValue(value BitVectorValue, additional int) BitVectorValue {
	if additional < 0 {
		panic("smt: negative bit-vector extension")
	}
	if value.width+additional <= 64 {
		return NewBitVectorUint64(value.width+additional, value.small)
	}
	return bitVectorValueFromBig(value.width+additional, value.big())
}

func SignExtendBitVectorValue(value BitVectorValue, additional int) BitVectorValue {
	if additional < 0 {
		panic("smt: negative bit-vector extension")
	}
	if !value.Bit(value.width - 1) {
		return ZeroExtendBitVectorValue(value, additional)
	}
	return bitVectorValueFromBig(value.width+additional, value.signedBig())
}

func RotateLeftBitVectorValue(value BitVectorValue, amount int) BitVectorValue {
	if amount < 0 {
		panic("smt: negative bit-vector rotation")
	}
	amount %= value.width
	if amount == 0 {
		return value
	}
	if value.width <= 64 {
		return NewBitVectorUint64(value.width, value.small<<amount|value.small>>(value.width-amount))
	}
	left := new(big.Int).Lsh(value.big(), uint(amount))
	right := new(big.Int).Rsh(value.big(), uint(value.width-amount))
	return bitVectorValueFromBig(value.width, left.Or(left, right))
}

func RotateRightBitVectorValue(value BitVectorValue, amount int) BitVectorValue {
	if amount < 0 {
		panic("smt: negative bit-vector rotation")
	}
	amount %= value.width
	if amount == 0 {
		return value
	}
	return RotateLeftBitVectorValue(value, value.width-amount)
}

func RepeatBitVectorValue(value BitVectorValue, count int) BitVectorValue {
	if count <= 0 {
		panic("smt: bit-vector repeat count must be positive")
	}
	if count == 1 {
		return value
	}
	width := value.width * count
	if width <= 64 {
		result := value.small
		for index := 1; index < count; index++ {
			result = result<<value.width | value.small
		}
		return NewBitVectorUint64(width, result)
	}
	result := value.big()
	part := value.big()
	for index := 1; index < count; index++ {
		result.Lsh(result, uint(value.width)).Or(result, part)
	}
	return bitVectorValueFromBig(width, result)
}

func UnsignedAddOverflowBitVectorValue(left, right BitVectorValue) bool {
	checkBitVectorWidths(left, right)
	if left.width <= 64 {
		_, carry := bits.Add64(left.small, right.small, 0)
		if left.width == 64 {
			return carry != 0
		}
		return carry != 0 || (left.small+right.small)>>left.width != 0
	}
	return new(big.Int).Add(left.big(), right.big()).BitLen() > left.width
}

func SignedAddOverflowBitVectorValue(left, right BitVectorValue) bool {
	checkBitVectorWidths(left, right)
	result := AddBitVectorValue(left, right)
	return left.Bit(left.width-1) == right.Bit(right.width-1) && result.Bit(result.width-1) != left.Bit(left.width-1)
}

func UnsignedSubOverflowBitVectorValue(left, right BitVectorValue) bool {
	return CompareUnsignedBitVectorValue(left, right) < 0
}

func SignedSubOverflowBitVectorValue(left, right BitVectorValue) bool {
	checkBitVectorWidths(left, right)
	result := SubBitVectorValue(left, right)
	return left.Bit(left.width-1) != right.Bit(right.width-1) && result.Bit(result.width-1) != left.Bit(left.width-1)
}

func UnsignedMulOverflowBitVectorValue(left, right BitVectorValue) bool {
	checkBitVectorWidths(left, right)
	if left.width <= 64 {
		high, low := bits.Mul64(left.small, right.small)
		if left.width == 64 {
			return high != 0
		}
		return high != 0 || low>>left.width != 0
	}
	return new(big.Int).Mul(left.big(), right.big()).BitLen() > left.width
}

func SignedMulOverflowBitVectorValue(left, right BitVectorValue) bool {
	checkBitVectorWidths(left, right)
	if left.width <= 64 {
		leftSigned := signedInlineBitVectorValue(left)
		rightSigned := signedInlineBitVectorValue(right)
		leftMagnitude, leftNegative := signedMagnitude(leftSigned)
		rightMagnitude, rightNegative := signedMagnitude(rightSigned)
		high, low := bits.Mul64(leftMagnitude, rightMagnitude)
		limit := uint64(1) << (left.width - 1)
		if left.width == 64 {
			limit = uint64(1) << 63
		}
		if leftNegative == rightNegative {
			limit--
		}
		return high != 0 || low > limit
	}
	product := new(big.Int).Mul(left.signedBig(), right.signedBig())
	limit := new(big.Int).Lsh(big.NewInt(1), uint(left.width-1))
	minimum := new(big.Int).Neg(new(big.Int).Set(limit))
	maximum := new(big.Int).Sub(limit, big.NewInt(1))
	return product.Cmp(minimum) < 0 || product.Cmp(maximum) > 0
}

func SignedDivOverflowBitVectorValue(left, right BitVectorValue) bool {
	checkBitVectorWidths(left, right)
	if left.width <= 64 {
		minimum := uint64(1) << (left.width - 1)
		minusOne := ^uint64(0)
		if left.width < 64 {
			minusOne = uint64(1)<<left.width - 1
		}
		return left.small == minimum && right.small == minusOne
	}
	return left.Bit(left.width-1) && left.big().BitLen() == left.width && left.big().Bit(left.width-1) != 0 &&
		left.big().Cmp(new(big.Int).Lsh(big.NewInt(1), uint(left.width-1))) == 0 &&
		EqualBitVectorValue(right, NotBitVectorValue(NewBitVectorUint64(right.width, 0)))
}

func NegOverflowBitVectorValue(value BitVectorValue) bool {
	if value.width <= 64 {
		return value.small == uint64(1)<<(value.width-1)
	}
	return value.Bit(value.width-1) && value.big().Cmp(new(big.Int).Lsh(big.NewInt(1), uint(value.width-1))) == 0
}

func signedInlineBitVectorValue(value BitVectorValue) int64 {
	if value.width == 64 {
		return int64(value.small)
	}
	shift := 64 - value.width
	return int64(value.small<<shift) >> shift
}

func signedMagnitude(value int64) (uint64, bool) {
	if value >= 0 {
		return uint64(value), false
	}
	return uint64(-(value + 1)) + 1, true
}

func checkBitVectorWidths(left, right BitVectorValue) {
	if left.width != right.width {
		panic("smt: bit-vector width mismatch")
	}
}

func BitVectorToIntegerValue(value BitVectorValue, signed bool) IntegerValue {
	if value.large == nil {
		if signed {
			if value.width == 64 {
				return NewIntegerValue(int64(value.small))
			}
			if value.Bit(value.width - 1) {
				return NewIntegerValue(int64(value.small) - int64(uint64(1)<<value.width))
			}
			return NewIntegerValue(int64(value.small))
		}
		if value.small <= uint64(^uint64(0)>>1) {
			return NewIntegerValue(int64(value.small))
		}
	}
	if signed {
		return integerValueFromBig(value.signedBig())
	}
	return integerValueFromBig(value.big())
}

func IntegerToBitVectorValue(width int, value IntegerValue) BitVectorValue {
	if width <= 0 {
		panic("smt: bit-vector width must be positive")
	}
	if width <= 64 && value.large == nil {
		return NewBitVectorUint64(width, uint64(value.small))
	}
	return bitVectorValueFromBig(width, value.big())
}

func NotBitVectorValue(value BitVectorValue) BitVectorValue {
	if value.width <= 64 && value.large == nil {
		result := ^value.small
		if value.width < 64 {
			result &= uint64(1)<<value.width - 1
		}
		return BitVectorValue{width: value.width, small: result}
	}
	mask := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), uint(value.width)), big.NewInt(1))
	result := new(big.Int).Xor(value.big(), mask)
	if value.width <= 64 {
		return BitVectorValue{width: value.width, small: result.Uint64()}
	}
	return BitVectorValue{width: value.width, large: result}
}

func binaryBitVectorValue(left, right BitVectorValue, large func(*big.Int, *big.Int) *big.Int, small func(uint64, uint64) uint64) BitVectorValue {
	if left.width != right.width {
		panic("smt: bit-vector width mismatch")
	}
	if left.width <= 64 {
		return NewBitVectorUint64(left.width, small(left.small, right.small))
	}
	result := large(left.big(), right.big())
	result.Mod(result, new(big.Int).Lsh(big.NewInt(1), uint(left.width)))
	return BitVectorValue{width: left.width, large: result}
}

func (value BitVectorValue) big() *big.Int {
	if value.large != nil {
		return new(big.Int).Set(value.large)
	}
	return new(big.Int).SetUint64(value.small)
}

func bitVectorValueFromBits(width int, bit func(int) bool) BitVectorValue {
	if width <= 64 {
		var value uint64
		for index := 0; index < width; index++ {
			if bit(index) {
				value |= uint64(1) << index
			}
		}
		return BitVectorValue{width: width, small: value}
	}
	value := new(big.Int)
	for index := 0; index < width; index++ {
		if bit(index) {
			value.SetBit(value, index, 1)
		}
	}
	return BitVectorValue{width: width, large: value}
}

// BitVectorTerm exposes an already validated exact value at the erased Go
// boundary used by SMT-LIB. Go+ callers normally use the indexed BitVecVal.
func BitVectorTerm(value BitVectorValue) Term[BitVecSort] {
	return bitVector[BitVecSort]{value: value}
}
