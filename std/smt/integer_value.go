package smt

import (
	"fmt"
	"math/big"
)

// IntegerValue is an exact mathematical integer. Values fitting int64 remain
// inline; larger magnitudes use an immutable arbitrary-precision payload.
type IntegerValue struct {
	small int64
	large *big.Int
}

func NewIntegerValue(value int64) IntegerValue { return IntegerValue{small: value} }

func ParseIntegerValue(text string) (IntegerValue, error) {
	value, ok := new(big.Int).SetString(text, 10)
	if !ok {
		return IntegerValue{}, fmt.Errorf("invalid integer %q", text)
	}
	return integerValueFromBig(value), nil
}

func (value IntegerValue) String() string {
	if value.large != nil {
		return value.large.String()
	}
	return fmt.Sprint(value.small)
}

func (value IntegerValue) Int64() (int64, bool) {
	if value.large != nil {
		return value.large.Int64(), value.large.IsInt64()
	}
	return value.small, true
}

func CompareIntegerValue(left, right IntegerValue) int {
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

func AddIntegerValue(left, right IntegerValue) IntegerValue {
	if left.large == nil && right.large == nil {
		result := left.small + right.small
		if (right.small > 0 && result < left.small) || (right.small < 0 && result > left.small) {
			return integerValueFromBig(new(big.Int).Add(left.big(), right.big()))
		}
		return NewIntegerValue(result)
	}
	return integerValueFromBig(new(big.Int).Add(left.big(), right.big()))
}

func NegateIntegerValue(value IntegerValue) IntegerValue {
	if value.large == nil && value.small != -1<<63 {
		return NewIntegerValue(-value.small)
	}
	return integerValueFromBig(new(big.Int).Neg(value.big()))
}

func SubIntegerValue(left, right IntegerValue) IntegerValue {
	return AddIntegerValue(left, NegateIntegerValue(right))
}

func MultiplyIntegerValue(left, right IntegerValue) IntegerValue {
	if left.large == nil && right.large == nil {
		if product, ok := checkedMulInt64(left.small, right.small); ok {
			return NewIntegerValue(product)
		}
	}
	return integerValueFromBig(new(big.Int).Mul(left.big(), right.big()))
}

// DivModIntegerValue implements SMT-LIB Euclidean division for every nonzero
// divisor: dividend = divisor*quotient + remainder and
// 0 <= remainder < abs(divisor).
func DivModIntegerValue(dividend, divisor IntegerValue) (IntegerValue, IntegerValue, bool) {
	divisorSign := CompareIntegerValue(divisor, IntegerValue{})
	if divisorSign == 0 {
		return IntegerValue{}, IntegerValue{}, false
	}
	if dividend.large == nil && divisor.large == nil && !(dividend.small == -1<<63 && divisor.small == -1) {
		quotient, remainder := dividend.small/divisor.small, dividend.small%divisor.small
		if remainder < 0 {
			if divisorSign > 0 {
				quotient--
				remainder += divisor.small
			} else {
				quotient++
				remainder -= divisor.small
			}
		}
		return NewIntegerValue(quotient), NewIntegerValue(remainder), true
	}
	quotient, remainder := new(big.Int), new(big.Int)
	quotient.QuoRem(dividend.big(), divisor.big(), remainder)
	if remainder.Sign() < 0 {
		if divisorSign > 0 {
			quotient.Sub(quotient, big.NewInt(1))
			remainder.Add(remainder, divisor.big())
		} else {
			quotient.Add(quotient, big.NewInt(1))
			remainder.Sub(remainder, divisor.big())
		}
	}
	return integerValueFromBig(quotient), integerValueFromBig(remainder), true
}

func (value IntegerValue) big() *big.Int {
	if value.large != nil {
		return new(big.Int).Set(value.large)
	}
	return big.NewInt(value.small)
}

func integerValueFromBig(value *big.Int) IntegerValue {
	if value.IsInt64() {
		return NewIntegerValue(value.Int64())
	}
	return IntegerValue{large: value}
}
