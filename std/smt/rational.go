package smt

import (
	"fmt"
	"math/big"
	"strings"
)

// Rational is an immutable arbitrary-precision rational. Its zero value is
// exactly zero. Operations never expose or mutate the retained big.Rat.
type Rational struct {
	numerator   int64
	denominator int64
	large       *big.Rat
}

func NewRational(numerator, denominator int64) Rational {
	if denominator == 0 {
		panic("smt: rational denominator is zero")
	}
	if value, ok := newSmallRational(numerator, denominator); ok {
		return value
	}
	return rationalFromBig(new(big.Rat).SetFrac(big.NewInt(numerator), big.NewInt(denominator)))
}

func ParseRational(text string) (Rational, error) {
	value := new(big.Rat)
	if _, ok := value.SetString(strings.TrimSpace(text)); !ok {
		return Rational{}, fmt.Errorf("smt: invalid rational %q", text)
	}
	return rationalFromBig(value), nil
}

func MustParseRational(text string) Rational {
	value, err := ParseRational(text)
	if err != nil {
		panic(err)
	}
	return value
}

func (value Rational) String() string {
	if numerator, denominator, ok := value.small(); ok {
		if denominator == 1 {
			return fmt.Sprintf("%d", numerator)
		}
		return fmt.Sprintf("%d/%d", numerator, denominator)
	}
	return value.large.RatString()
}
func (value Rational) Numerator() string   { return value.big().Num().String() }
func (value Rational) Denominator() string { return value.big().Denom().String() }
func (value Rational) Sign() int {
	if numerator, _, ok := value.small(); ok {
		switch {
		case numerator < 0:
			return -1
		case numerator > 0:
			return 1
		default:
			return 0
		}
	}
	return value.large.Sign()
}
func (value Rational) IsInteger() bool {
	if _, denominator, ok := value.small(); ok {
		return denominator == 1
	}
	return value.large.IsInt()
}
func DivideRational(left, right Rational) Rational { return rationalQuo(left, right) }
func AddRational(left, right Rational) Rational    { return rationalAdd(left, right) }
func SubtractRational(left, right Rational) Rational {
	return rationalSub(left, right)
}
func MultiplyRational(left, right Rational) Rational { return rationalMul(left, right) }
func NegateRational(value Rational) Rational         { return rationalNeg(value) }
func CompareRational(left, right Rational) int       { return rationalCmp(left, right) }

func RationalFromInteger(value IntegerValue) Rational {
	if value.large == nil {
		return NewRational(value.small, 1)
	}
	return rationalFromBig(new(big.Rat).SetInt(value.large))
}

func RationalNumerator(value Rational) IntegerValue {
	if numerator, _, ok := value.small(); ok {
		return NewIntegerValue(numerator)
	}
	return integerValueFromBig(new(big.Int).Set(value.large.Num()))
}

func RationalDenominator(value Rational) IntegerValue {
	if _, denominator, ok := value.small(); ok {
		return NewIntegerValue(denominator)
	}
	return integerValueFromBig(new(big.Int).Set(value.large.Denom()))
}

func FloorRational(value Rational) IntegerValue {
	if numerator, denominator, ok := value.small(); ok {
		quotient := numerator / denominator
		if numerator < 0 && numerator%denominator != 0 {
			quotient--
		}
		return NewIntegerValue(quotient)
	}
	numerator, denominator := value.large.Num(), value.large.Denom()
	var quotient, remainder big.Int
	quotient.QuoRem(numerator, denominator, &remainder)
	if numerator.Sign() < 0 && remainder.Sign() != 0 {
		quotient.Sub(&quotient, big.NewInt(1))
	}
	return integerValueFromBig(&quotient)
}

func ExactRealConstant(term Term[RealSort]) (Rational, bool) {
	switch value := term.(type) {
	case Real:
		return value.Value, true
	case integerToReal:
		integer, ok := ExactIntegerConstant(value.value)
		if !ok {
			return Rational{}, false
		}
		return RationalFromInteger(integer), true
	case RealAdd:
		result := Rational{}
		for _, item := range value.Values {
			next, ok := ExactRealConstant(item)
			if !ok {
				return Rational{}, false
			}
			result = AddRational(result, next)
		}
		return result, true
	case RealSubtract:
		left, leftOK := ExactRealConstant(value.Left)
		right, rightOK := ExactRealConstant(value.Right)
		if !leftOK || !rightOK {
			return Rational{}, false
		}
		return SubtractRational(left, right), true
	case RealScale:
		item, ok := ExactRealConstant(value.Value)
		if !ok {
			return Rational{}, false
		}
		return MultiplyRational(value.Coefficient, item), true
	default:
		return Rational{}, false
	}
}

func (value Rational) big() *big.Rat {
	if numerator, denominator, ok := value.small(); ok {
		return new(big.Rat).SetFrac(big.NewInt(numerator), big.NewInt(denominator))
	}
	return new(big.Rat).Set(value.large)
}

func rationalFromBig(value *big.Rat) Rational {
	if value.Sign() == 0 {
		return Rational{}
	}
	if value.Num().IsInt64() && value.Denom().IsInt64() {
		if small, ok := newSmallRational(value.Num().Int64(), value.Denom().Int64()); ok {
			return small
		}
	}
	return Rational{large: new(big.Rat).Set(value)}
}

func rationalAdd(left, right Rational) Rational {
	leftNumerator, leftDenominator, leftOK := left.small()
	rightNumerator, rightDenominator, rightOK := right.small()
	if leftOK && rightOK {
		common := gcdUint64(absUint64(leftDenominator), absUint64(rightDenominator))
		leftScale := rightDenominator / int64(common)
		rightScale := leftDenominator / int64(common)
		leftPart, leftProductOK := checkedMulInt64(leftNumerator, leftScale)
		rightPart, rightProductOK := checkedMulInt64(rightNumerator, rightScale)
		numerator, sumOK := checkedAddInt64(leftPart, rightPart)
		denominator, denominatorOK := checkedMulInt64(leftDenominator, leftScale)
		if leftProductOK && rightProductOK && sumOK && denominatorOK {
			return NewRational(numerator, denominator)
		}
	}
	return rationalFromBig(new(big.Rat).Add(left.big(), right.big()))
}

func rationalSub(left, right Rational) Rational {
	return rationalAdd(left, rationalNeg(right))
}

func rationalMul(left, right Rational) Rational {
	leftNumerator, leftDenominator, leftOK := left.small()
	rightNumerator, rightDenominator, rightOK := right.small()
	if leftOK && rightOK {
		leftCancel := int64(gcdUint64(absUint64(leftNumerator), absUint64(rightDenominator)))
		rightCancel := int64(gcdUint64(absUint64(rightNumerator), absUint64(leftDenominator)))
		leftNumerator /= leftCancel
		rightDenominator /= leftCancel
		rightNumerator /= rightCancel
		leftDenominator /= rightCancel
		numerator, numeratorOK := checkedMulInt64(leftNumerator, rightNumerator)
		denominator, denominatorOK := checkedMulInt64(leftDenominator, rightDenominator)
		if numeratorOK && denominatorOK {
			return NewRational(numerator, denominator)
		}
	}
	return rationalFromBig(new(big.Rat).Mul(left.big(), right.big()))
}

func rationalNeg(value Rational) Rational {
	if numerator, denominator, ok := value.small(); ok && numerator != -1<<63 {
		return Rational{numerator: -numerator, denominator: denominator}
	}
	return rationalFromBig(new(big.Rat).Neg(value.big()))
}

func rationalQuo(left, right Rational) Rational {
	if right.Sign() == 0 {
		panic("smt: rational division by zero")
	}
	if rightNumerator, rightDenominator, ok := right.small(); ok {
		return rationalMul(left, NewRational(rightDenominator, rightNumerator))
	}
	return rationalFromBig(new(big.Rat).Quo(left.big(), right.big()))
}

func rationalCmp(left, right Rational) int {
	leftNumerator, leftDenominator, leftOK := left.small()
	rightNumerator, rightDenominator, rightOK := right.small()
	if leftOK && rightOK {
		leftProduct, leftProductOK := checkedMulInt64(leftNumerator, rightDenominator)
		rightProduct, rightProductOK := checkedMulInt64(rightNumerator, leftDenominator)
		if leftProductOK && rightProductOK {
			switch {
			case leftProduct < rightProduct:
				return -1
			case leftProduct > rightProduct:
				return 1
			default:
				return 0
			}
		}
	}
	return left.big().Cmp(right.big())
}

func (value Rational) small() (int64, int64, bool) {
	if value.large != nil {
		return 0, 0, false
	}
	if value.denominator == 0 {
		return 0, 1, true
	}
	return value.numerator, value.denominator, true
}

func newSmallRational(numerator, denominator int64) (Rational, bool) {
	if denominator == 0 || denominator == -1<<63 || numerator == -1<<63 && denominator < 0 {
		return Rational{}, false
	}
	if denominator < 0 {
		numerator = -numerator
		denominator = -denominator
	}
	if numerator == 0 {
		return Rational{}, true
	}
	divisor := int64(gcdUint64(absUint64(numerator), uint64(denominator)))
	return Rational{numerator: numerator / divisor, denominator: denominator / divisor}, true
}

func checkedAddInt64(left, right int64) (int64, bool) {
	result := left + right
	return result, (right >= 0 || result < left) && (right <= 0 || result > left)
}

func checkedMulInt64(left, right int64) (int64, bool) {
	if left == 0 || right == 0 {
		return 0, true
	}
	if left == -1 && right == -1<<63 || right == -1 && left == -1<<63 {
		return 0, false
	}
	result := left * right
	return result, result/right == left
}

func absUint64(value int64) uint64 {
	if value < 0 {
		return uint64(-(value + 1)) + 1
	}
	return uint64(value)
}

func gcdUint64(left, right uint64) uint64 {
	for right != 0 {
		left, right = right, left%right
	}
	if left == 0 {
		return 1
	}
	return left
}

type rationalModelEntry struct {
	id    int
	value Rational
}

type rationalModel struct {
	count    int
	inline   [4]rationalModelEntry
	overflow []rationalModelEntry
}

func (model *rationalModel) set(id int, value Rational) {
	entries := model.entries()
	for index := range entries {
		if entries[index].id == id {
			entries[index].value = value
			return
		}
	}
	if model.count < len(model.inline) && model.overflow == nil {
		model.inline[model.count] = rationalModelEntry{id: id, value: value}
		model.count++
		return
	}
	if model.overflow == nil {
		model.overflow = make([]rationalModelEntry, model.count, model.count*2)
		copy(model.overflow, model.inline[:model.count])
	}
	model.overflow = append(model.overflow, rationalModelEntry{id: id, value: value})
	model.count++
}

func (model rationalModel) lookup(id int) (Rational, bool) {
	for _, entry := range model.entries() {
		if entry.id == id {
			return entry.value, true
		}
	}
	return Rational{}, false
}

func (model *rationalModel) merge(other rationalModel) {
	for _, entry := range other.entries() {
		model.set(entry.id, entry.value)
	}
}

func (model *rationalModel) entries() []rationalModelEntry {
	if model.overflow != nil {
		return model.overflow[:model.count]
	}
	return model.inline[:model.count]
}
