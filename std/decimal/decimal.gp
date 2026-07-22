// Package decimal implements immutable arbitrary-precision base-10 decimals.
//
// Decimal values use coefficient * 10^exponent.  Arithmetic never passes
// through binary floating point.  Operations which can lose information take
// an explicit rounding mode; Divide reports whether rounding was necessary.
//
// The package is authored in Go+.  Its generated Go is the distribution API.
package decimal

import (
	"fmt"
	"math/big"
	"strconv"
	"strings"
)

// Precision is a positive, deliberately bounded number of decimal places.
// The bound prevents an untrusted plain-Go caller from requesting an
// unreasonable power-of-ten allocation at an exported boundary.
type Precision refine(value int32) { value > 0 && value <= 1000000 }

// Scale bounds public digit/exponent work so untrusted Go callers cannot turn
// a formatting or rounding request into a multi-gigabyte allocation.
type Scale refine(value int32) { value >= -1000000 && value <= 1000000 }

// RoundingMode makes every lossy operation state its tie and direction rule.
type RoundingMode enum {
	HalfAwayFromZero()
	HalfEven()
	TowardZero()
	AwayFromZero()
	TowardNegative()
	TowardPositive()
}

// DivisionResult distinguishes exact arithmetic, an explicitly rounded
// result, and division by zero.
//goplus:derive off
type DivisionResult enum {
	Exact(Value Decimal)
	Rounded(Value Decimal)
	DivisionByZero()
}

// Decimal is immutable. Its zero value is numeric zero.
type Decimal struct {
	coefficient *big.Int
	exponent int32
}

var Zero = New(0, 0)
var One = New(1, 0)
var Ten = New(10, 0)

// smallPowersOfTen is deliberately bounded. Values are immutable after
// initialization and are only ever passed to big.Int operations as operands,
// never as receivers. The table covers ordinary financial scales without the
// unbounded-memory behavior of a dynamic cache.
var smallPowersOfTen = func() []*big.Int {
	powers := make([]*big.Int, 65)
	powers[0] = big.NewInt(1)
	ten := big.NewInt(10)
	for i := 1; i < len(powers); i++ {
		powers[i] = new(big.Int).Mul(powers[i-1], ten)
	}
	return powers
}()

var immutableZeroCoefficient = new(big.Int)

// New constructs coefficient * 10^exponent.
func New(coefficient int64, exponent int32) Decimal {
	return fromOwned(big.NewInt(coefficient), exponent)
}

func NewFromInt(value int64) Decimal { return New(value, 0) }
func NewFromInt32(value int32) Decimal { return New(int64(value), 0) }

func NewFromUint64(value uint64) Decimal {
	return fromOwned(new(big.Int).SetUint64(value), 0)
}

// NewFromFloat converts the shortest round-trippable decimal representation
// of a finite binary64 value. It rejects NaN and infinities.
func NewFromFloat(value float64) (Decimal, error) {
	text := strconv.FormatFloat(value, 'g', -1, 64)
	if text == "NaN" || text == "+Inf" || text == "-Inf" {
		return Decimal{}, fmt.Errorf("decimal: cannot convert non-finite float %s", text)
	}
	return NewFromString(text)
}

// NewFromBigInt copies coefficient; subsequent caller mutation is harmless.
func NewFromBigInt(coefficient *big.Int, exponent int32) Decimal {
	if coefficient == nil { return Zero }
	return fromBigInt(coefficient, exponent)
}

// NewFromBigRat divides numerator by denominator with the requested positive
// fractional precision and half-away-from-zero rounding.
func NewFromBigRat(value *big.Rat, precision Precision) Decimal {
	if value == nil { return Zero }
	result := NewFromBigInt(value.Num(), 0).Divide(NewFromBigInt(value.Denom(), 0), precision, HalfAwayFromZero{})
	if exact, ok := result.(Exact); ok { return exact.Value }
	// A big.Rat denominator is non-zero by construction, so the remaining
	// result is Rounded. Keep the invariant as a checked assertion.
	return result.(Rounded).Value
}

func fromBigInt(coefficient *big.Int, exponent int32) Decimal {
	return Decimal{coefficient: new(big.Int).Set(coefficient), exponent: exponent}
}

// fromOwned adopts a fresh coefficient which is unreachable by the caller.
// Public constructors always copy; arithmetic can avoid copying its own result.
func fromOwned(coefficient *big.Int, exponent int32) Decimal {
	if coefficient == nil { coefficient = new(big.Int) }
	return Decimal{coefficient: coefficient, exponent: exponent}
}

func (d Decimal) coeff() *big.Int {
	return new(big.Int).Set(d.coeffView())
}

// coeffView is internal read-only access. Decimal's immutability relies on
// never using this pointer as a big.Int receiver; exported accessors still
// return defensive copies through coeff.
func (d Decimal) coeffView() *big.Int {
	if d.coefficient == nil { return immutableZeroCoefficient }
	return d.coefficient
}

// NewFromString accepts ordinary and scientific decimal notation. It retains
// the written fractional scale, while String emits the shortest value-preserving
// representation.
func NewFromString(input string) (Decimal, error) {
	if input == "" { return Decimal{}, fmt.Errorf("decimal: empty input") }
	mantissa, scientific := input, int64(0)
	if i := strings.IndexAny(mantissa, "eE"); i >= 0 {
		if strings.IndexAny(mantissa[i+1:], "eE") >= 0 || i == len(mantissa)-1 {
			return Decimal{}, fmt.Errorf("decimal: invalid exponent in %q", input)
		}
		var err error
		scientific, err = strconv.ParseInt(mantissa[i+1:], 10, 32)
		if err != nil { return Decimal{}, fmt.Errorf("decimal: invalid exponent in %q", input) }
		mantissa = mantissa[:i]
	}

	sign := ""
	if len(mantissa) > 0 && (mantissa[0] == '+' || mantissa[0] == '-') {
		sign, mantissa = mantissa[:1], mantissa[1:]
	}
	if mantissa == "" { return Decimal{}, fmt.Errorf("decimal: invalid syntax %q", input) }
	point := strings.IndexByte(mantissa, '.')
	if point >= 0 && strings.IndexByte(mantissa[point+1:], '.') >= 0 {
		return Decimal{}, fmt.Errorf("decimal: invalid syntax %q", input)
	}
	fractional := int64(0)
	digits := mantissa
	if point >= 0 {
		fractional = int64(len(mantissa) - point - 1)
		digits = mantissa[:point] + mantissa[point+1:]
	}
	if digits == "" { return Decimal{}, fmt.Errorf("decimal: invalid syntax %q", input) }
	for _, r := range digits {
		if r < '0' || r > '9' { return Decimal{}, fmt.Errorf("decimal: invalid syntax %q", input) }
	}
	exponent, err := parseExponent(scientific-fractional, input)
	if err != nil { return Decimal{}, err }
	// SetString cannot fail after the explicit ASCII digit validation above.
	c, _ := new(big.Int).SetString(sign+digits, 10)
	return fromOwned(c, exponent), nil
}

func parseExponent(exponent int64, input string) (int32, error) {
	if exponent < -2147483648 || exponent > 2147483647 {
		return 0, fmt.Errorf("decimal: exponent out of range in %q", input)
	}
	return int32(exponent), nil
}

func RequireFromString(value string) Decimal {
	d, err := NewFromString(value)
	if err != nil { panic(err) }
	return d
}

func (d Decimal) Coefficient() *big.Int { return d.coeff() }
func (d Decimal) CoefficientInt64() int64 { return d.coeff().Int64() }
func (d Decimal) Exponent() int32 { return d.exponent }
func (d Decimal) Sign() int { return d.coeff().Sign() }
func (d Decimal) IsZero() bool { return d.Sign() == 0 }
func (d Decimal) IsPositive() bool { return d.Sign() > 0 }
func (d Decimal) IsNegative() bool { return d.Sign() < 0 }
func (d Decimal) Copy() Decimal { return fromBigInt(d.coeff(), d.exponent) }
func (d Decimal) Neg() Decimal { return fromOwned(new(big.Int).Neg(d.coeff()), d.exponent) }
func (d Decimal) Abs() Decimal { return fromOwned(new(big.Int).Abs(d.coeff()), d.exponent) }
func (d Decimal) Shift(places int32) Decimal { return fromOwned(d.coeff(), checkedExponent(int64(d.exponent)+int64(places))) }

func checkedExponent(exponent int64) int32 {
	if exponent < -2147483648 || exponent > 2147483647 { panic("decimal: exponent overflow") }
	return int32(exponent)
}

func pow10(n int64) *big.Int {
	if n < 0 { panic("decimal: negative power") }
	if n < int64(len(smallPowersOfTen)) { return smallPowersOfTen[n] }
	return new(big.Int).Exp(big.NewInt(10), big.NewInt(n), nil)
}

func align(a, b Decimal) (*big.Int, *big.Int, int32) {
	exp := a.exponent
	if b.exponent < exp { exp = b.exponent }
	ac, bc := a.coeffView(), b.coeffView()
	if a.exponent > exp { ac = new(big.Int).Mul(ac, pow10(int64(a.exponent-exp))) }
	if b.exponent > exp { bc = new(big.Int).Mul(bc, pow10(int64(b.exponent-exp))) }
	return ac, bc, exp
}

func (d Decimal) Add(other Decimal) Decimal {
	a, b, exp := align(d, other)
	return fromOwned(new(big.Int).Add(a, b), exp)
}

func (d Decimal) Sub(other Decimal) Decimal {
	a, b, exp := align(d, other)
	return fromOwned(new(big.Int).Sub(a, b), exp)
}

func (d Decimal) Mul(other Decimal) Decimal {
	exp := checkedExponent(int64(d.exponent)+int64(other.exponent))
	return fromOwned(new(big.Int).Mul(d.coeffView(), other.coeffView()), exp)
}

func (d Decimal) Cmp(other Decimal) int {
	a, b, _ := align(d, other)
	return a.Cmp(b)
}

func (d Decimal) Compare(other Decimal) int { return d.Cmp(other) }
func (d Decimal) Equal(other Decimal) bool { return d.Cmp(other) == 0 }
func (d Decimal) Equals(other Decimal) bool { return d.Equal(other) }
func (d Decimal) LessThan(other Decimal) bool { return d.Cmp(other) < 0 }
func (d Decimal) GreaterThan(other Decimal) bool { return d.Cmp(other) > 0 }
func (d Decimal) GreaterThanOrEqual(other Decimal) bool { return d.Cmp(other) >= 0 }
func (d Decimal) LessThanOrEqual(other Decimal) bool { return d.Cmp(other) <= 0 }

// Round returns d rounded to places digits after the decimal point.
func (d Decimal) Round(places Scale, mode RoundingMode) Decimal { return d.round(places, mode) }

func (d Decimal) round(places int32, mode RoundingMode) Decimal {
	target := checkedExponent(-int64(places))
	if d.exponent >= target { return d }
	divisor := pow10(int64(target) - int64(d.exponent))
	q, r := new(big.Int), new(big.Int)
	q.QuoRem(d.coeff(), divisor, r)
	if shouldIncrement(q, r, divisor, mode) {
		if d.Sign() < 0 { q.Sub(q, big.NewInt(1)) } else { q.Add(q, big.NewInt(1)) }
	}
	return fromOwned(q, target)
}

func shouldIncrement(q, remainder, divisor *big.Int, mode RoundingMode) bool {
	if remainder.Sign() == 0 { return false }
	switch any(mode).(type) {
	case TowardZero:
		return false
	case AwayFromZero:
		return true
	case TowardNegative:
		return remainder.Sign() < 0
	case TowardPositive:
		return remainder.Sign() > 0
	case HalfAwayFromZero, HalfEven:
		twice := new(big.Int).Lsh(new(big.Int).Abs(remainder), 1)
		cmp := twice.Cmp(divisor)
		if cmp > 0 { return true }
		if cmp < 0 { return false }
		if _, ok := any(mode).(HalfAwayFromZero); ok { return true }
		return q.Bit(0) == 1
	default:
		panic("decimal: impossible rounding mode")
	}
}

// Divide produces a decimal with at most places fractional digits and reports
// whether information was discarded. Division by zero is a value, not a panic.
func (d Decimal) Divide(other Decimal, places Precision, mode RoundingMode) DivisionResult {
	target := -places
	numerator, denominator := d.coeff(), other.coeff()
	if denominator.Sign() == 0 { return DivisionByZero{} }
	if denominator.Sign() < 0 {
		numerator.Neg(numerator)
		denominator.Neg(denominator)
	}
	shift := int64(d.exponent) - int64(other.exponent) - int64(target)
	if shift >= 0 { numerator.Mul(numerator, pow10(shift)) } else { denominator.Mul(denominator, pow10(-shift)) }
	q, r := new(big.Int), new(big.Int)
	q.QuoRem(numerator, denominator, r)
	if r.Sign() == 0 { return Exact{Value: fromOwned(q, target)} }
	if shouldIncrement(q, r, new(big.Int).Abs(denominator), mode) {
		negative := numerator.Sign() < 0
		if negative { q.Sub(q, big.NewInt(1)) } else { q.Add(q, big.NewInt(1)) }
	}
	return Rounded{Value: fromOwned(q, target)}
}

// Mod returns the truncated-quotient remainder and panics on a zero divisor,
// matching Go's integer remainder convention.
func (d Decimal) Mod(other Decimal) Decimal {
	a, b, exp := align(d, other)
	if b.Sign() == 0 { panic("decimal: remainder by zero") }
	quotient := new(big.Int).Quo(a, b)
	remainder := new(big.Int).Sub(a, new(big.Int).Mul(quotient, b))
	return fromOwned(remainder, exp)
}

func (d Decimal) Truncate(places Scale) Decimal { return d.round(places, TowardZero{}) }
func (d Decimal) Floor() Decimal { return d.round(0, TowardNegative{}) }
func (d Decimal) Ceil() Decimal { return d.round(0, TowardPositive{}) }
func (d Decimal) RoundBank(places Scale) Decimal { return d.round(places, HalfEven{}) }
func (d Decimal) RoundDown(places Scale) Decimal { return d.round(places, TowardZero{}) }
func (d Decimal) RoundUp(places Scale) Decimal { return d.round(places, AwayFromZero{}) }
func (d Decimal) RoundFloor(places Scale) Decimal { return d.round(places, TowardNegative{}) }
func (d Decimal) RoundCeil(places Scale) Decimal { return d.round(places, TowardPositive{}) }

// IntPart truncates toward zero.
func (d Decimal) IntPart() int64 {
	integer := d.Truncate(0)
	c := integer.coeff()
	if integer.exponent > 0 { c.Mul(c, pow10(int64(integer.exponent))) }
	return c.Int64()
}

// BigInt returns d truncated toward zero as an arbitrary-precision integer.
func (d Decimal) BigInt() *big.Int {
	integer := d.Truncate(0)
	c := integer.coeff()
	if integer.exponent > 0 { c.Mul(c, pow10(int64(integer.exponent))) }
	return c
}

func (d Decimal) Rat() *big.Rat {
	numerator := d.coeff()
	denominator := big.NewInt(1)
	if d.exponent >= 0 { numerator.Mul(numerator, pow10(int64(d.exponent))) } else { denominator = pow10(-int64(d.exponent)) }
	return new(big.Rat).SetFrac(numerator, denominator)
}

func (d Decimal) BigFloat() *big.Float { return new(big.Float).SetRat(d.Rat()) }

// Float64 returns the nearest binary64 value and whether it is exact.
func (d Decimal) Float64() (float64, bool) {
	return d.Rat().Float64()
}

func (d Decimal) InexactFloat64() float64 { value, _ := d.Float64(); return value }

func (d Decimal) IsInteger() bool { return d.Equal(fromOwned(d.BigInt(), 0)) }

func (d Decimal) NumDigits() int {
	c := d.coeff()
	if c.Sign() < 0 { c.Abs(c) }
	if c.Sign() == 0 { return 1 }
	return len(c.String())
}

func (d Decimal) String() string {
	c := d.coeff()
	if c.Sign() == 0 { return "0" }
	negative := c.Sign() < 0
	if negative { c.Abs(c) }
	digits := c.String()
	var out string
	if d.exponent >= 0 {
		out = digits + strings.Repeat("0", int(d.exponent))
	} else {
		point := len(digits) + int(d.exponent)
		if point > 0 { out = digits[:point] + "." + digits[point:] } else { out = "0." + strings.Repeat("0", -point) + digits }
		out = strings.TrimRight(strings.TrimRight(out, "0"), ".")
	}
	if negative { return "-" + out }
	return out
}

// StringFixed rounds half away from zero and prints exactly places digits
// after the decimal point.
func (d Decimal) StringFixed(places Scale) string {
	return d.stringFixed(places, HalfAwayFromZero{})
}

func (d Decimal) StringFixedBank(places Scale) string { return d.stringFixed(places, HalfEven{}) }

func (d Decimal) stringFixed(places int32, mode RoundingMode) string {
	if places < 0 { return d.round(places, mode).String() }
	target := -places
	rounded := d.round(places, mode)
	c := rounded.coeff()
	if rounded.exponent > target { c.Mul(c, pow10(int64(rounded.exponent-target))) }
	negative := c.Sign() < 0
	if negative { c.Abs(c) }
	digits := c.String()
	if places == 0 {
		if negative { return "-" + digits }
		return digits
	}
	point := len(digits) - int(places)
	out := ""
	if point > 0 { out = digits[:point] + "." + digits[point:] } else { out = "0." + strings.Repeat("0", -point) + digits }
	if negative { return "-" + out }
	return out
}

// RescalePair returns numerically equal representations at the smaller
// exponent, the representation required for coefficient-wise operations.
func RescalePair(left Decimal, right Decimal) (Decimal, Decimal) {
	a, b, exp := align(left, right)
	return fromOwned(a, exp), fromOwned(b, exp)
}

func Min(first Decimal, rest ...Decimal) Decimal {
	result := first
	for _, value := range rest { if value.LessThan(result) { result = value } }
	return result
}

func Max(first Decimal, rest ...Decimal) Decimal {
	result := first
	for _, value := range rest { if value.GreaterThan(result) { result = value } }
	return result
}

func Sum(first Decimal, rest ...Decimal) Decimal {
	result := first
	for _, value := range rest { result = result.Add(value) }
	return result
}

// Average computes a mean under an explicit precision and rounding policy.
// An empty input returns DivisionByZero because its divisor is zero.
func Average(values []Decimal, precision Precision, mode RoundingMode) DivisionResult {
	if len(values) == 0 { return DivisionByZero{} }
	total := Zero
	for _, value := range values { total = total.Add(value) }
	return total.Divide(NewFromInt(int64(len(values))), precision, mode)
}

// Fixed is a decimal whose non-negative number of fractional places is an
// erased type index. Plain Go sees Fixed as an ordinary sealed sum; Go+ keeps p.
//goplus:derive off
type Fixed[p nat] enum {
	fixedValue(Places int, Value Decimal) Fixed[p]
}

// Quantize constructs a Fixed[p], rounding exactly once at the boundary.
func Quantize(p nat, d Decimal, mode RoundingMode) Fixed[p] {
	if p < 0 || p > 1000000 { panic("decimal: places out of range") }
	return fixedValue(p, d.round(int32(p), mode))
}

// FixedDecimal reveals the ordinary runtime decimal without changing p.
func FixedDecimal(0 p nat, value Fixed[p]) Decimal {
	match value {
	case fixedValue(_, d):
		return d
	}
}

// FixedPlaces returns the runtime witness retained for ordinary Go callers.
func FixedPlaces(0 p nat, value Fixed[p]) int {
	match value {
	case fixedValue(places, _):
		return places
	}
}

// AddFixed preserves a shared scale index.
func AddFixed(0 p nat, left Fixed[p], right Fixed[p]) Fixed[p] {
	match left {
	case fixedValue(pa, a):
		match right {
		case fixedValue(pb, b):
			if pa != pb { panic("decimal: AddFixed scale mismatch") }
			return fixedValue(pa, a.Add(b))
		}
	}
}

// SubFixed preserves a shared scale index.
func SubFixed(0 p nat, left Fixed[p], right Fixed[p]) Fixed[p] {
	match left {
	case fixedValue(pa, a):
		match right {
		case fixedValue(pb, b):
			if pa != pb { panic("decimal: SubFixed scale mismatch") }
			return fixedValue(pa, a.Sub(b))
		}
	}
}

// NegFixed preserves scale.
func NegFixed(0 p nat, value Fixed[p]) Fixed[p] {
	match value {
	case fixedValue(places, d):
		return fixedValue(places, d.Neg())
	}
}

// MulFixed adds the operands' scale indices. The arithmetic relation is
// checked before erasure and reconstructed across package boundaries.
func MulFixed(0 p nat, 0 q nat, left Fixed[p], right Fixed[q]) Fixed[p+q] {
	match left {
	case fixedValue(pa, a):
		match right {
		case fixedValue(pb, b):
			return fixedValue(pa+pb, a.Mul(b))
		}
	}
}

// RescaleFixed is an explicit lossy boundary from Fixed[p] to Fixed[q].
func RescaleFixed(0 p nat, q nat, value Fixed[p], mode RoundingMode) Fixed[q] {
	if q < 0 || q > 1000000 { panic("decimal: places out of range") }
	match value {
	case fixedValue(_, d):
		return fixedValue(q, d.round(int32(q), mode))
	}
}

// CompareFixed compares values at arbitrary scales without changing either.
func CompareFixed(0 p nat, 0 q nat, left Fixed[p], right Fixed[q]) int {
	match left {
	case fixedValue(_, a):
		match right {
		case fixedValue(_, b):
			return a.Cmp(b)
		}
	}
}
