package decimal

import (
	"bytes"
	"encoding/gob"
	"math"
	"math/big"
	"reflect"
	"testing"
)

type invalidRoundingMode struct{}

func (invalidRoundingMode) isRoundingMode() {}

type invalidFixed struct{}

func (invalidFixed) isFixed() {}

func mustPanic(t *testing.T, fn func()) {
	t.Helper()
	defer func() {
		if recover() == nil {
			t.Fatal("expected panic")
		}
	}()
	fn()
}

func TestConstructorsPredicatesAndRepresentations(t *testing.T) {
	if NewFromInt32(-12).String() != "-12" || NewFromUint64(math.MaxUint64).String() != "18446744073709551615" {
		t.Fatal("integer constructor mismatch")
	}
	for _, value := range []float64{math.NaN(), math.Inf(1), math.Inf(-1)} {
		if _, err := NewFromFloat(value); err == nil {
			t.Fatalf("NewFromFloat(%v) succeeded", value)
		}
	}
	if !NewFromBigInt(nil, 4).IsZero() || !NewFromBigRat(nil, 4).IsZero() {
		t.Fatal("nil constructor is not zero")
	}

	d := RequireFromString("-12.30")
	if !d.IsNegative() || d.IsPositive() || d.IsZero() || !d.Copy().Equal(d) || d.Abs().String() != "12.3" || d.Neg().String() != "12.3" {
		t.Fatal("predicate/copy/sign operation mismatch")
	}
	if d.Shift(2).String() != "-1230" || d.NumDigits() != 4 || Zero.NumDigits() != 1 {
		t.Fatal("shift/digit mismatch")
	}
	if !One.IsPositive() || !Zero.IsZero() || One.Compare(Ten) >= 0 || !One.Equals(One) || !Ten.GreaterThanOrEqual(One) || !One.LessThanOrEqual(Ten) {
		t.Fatal("comparison alias mismatch")
	}
	if RequireFromString("12.9").IntPart() != 12 || New(12, 2).BigInt().Cmp(big.NewInt(1200)) != 0 {
		t.Fatal("integer conversion mismatch")
	}
	if RequireFromString("1.5").BigFloat().Cmp(big.NewFloat(1.5)) != 0 || RequireFromString("1.5").InexactFloat64() != 1.5 {
		t.Fatal("floating conversion mismatch")
	}
}

func TestParsingAndBoundsFailures(t *testing.T) {
	invalid := []string{"", "+", "1e", "1e2e3", "1e999999999999", "1.2.3", ".", "1x", "1e2147483648", "1e-2147483649", "1.0e-2147483648"}
	for _, input := range invalid {
		if _, err := NewFromString(input); err == nil {
			t.Fatalf("NewFromString(%q) succeeded", input)
		}
	}
	mustPanic(t, func() { RequireFromString("bad") })
	mustPanic(t, func() { _ = New(1, 1).Shift(math.MaxInt32) })
	mustPanic(t, func() { _ = pow10(-1) })
	mustPanic(t, func() { _ = New(1, math.MaxInt32).Mul(New(1, 1)) })
}

func TestConvenienceRoundingAndFormatting(t *testing.T) {
	d := RequireFromString("-12.55")
	wants := []struct {
		got, want string
	}{
		{d.Truncate(1).String(), "-12.5"}, {d.Floor().String(), "-13"},
		{d.Ceil().String(), "-12"}, {d.RoundBank(1).String(), "-12.6"},
		{d.RoundDown(1).String(), "-12.5"}, {d.RoundUp(1).String(), "-12.6"},
		{d.RoundFloor(1).String(), "-12.6"}, {d.RoundCeil(1).String(), "-12.5"},
		{d.StringFixed(-1), "-10"}, {New(-12, 1).StringFixed(0), "-120"},
	}
	for _, item := range wants {
		if item.got != item.want {
			t.Fatalf("got %q, want %q", item.got, item.want)
		}
	}
	mustPanic(t, func() { _ = shouldIncrement(new(big.Int), big.NewInt(1), big.NewInt(2), invalidRoundingMode{}) })
	mustPanic(t, func() { _ = One.Mod(Zero) })

	a, b := RescalePair(New(1, 1), New(2, 0))
	if a.Exponent() != 0 || b.Exponent() != 0 || !a.Equal(Ten) || !b.Equal(NewFromInt(2)) {
		t.Fatal("RescalePair mismatch")
	}
}

func TestGeneratedRoundingModeHelpers(t *testing.T) {
	HalfAwayFromZero{}.isRoundingMode()
	HalfEven{}.isRoundingMode()
	TowardZero{}.isRoundingMode()
	AwayFromZero{}.isRoundingMode()
	TowardNegative{}.isRoundingMode()
	TowardPositive{}.isRoundingMode()
	Exact{}.isDivisionResult()
	Rounded{}.isDivisionResult()
	DivisionByZero{}.isDivisionResult()
	fixedValue{}.isFixed()
	modes := []RoundingMode{HalfAwayFromZero{}, HalfEven{}, TowardZero{}, AwayFromZero{}, TowardNegative{}, TowardPositive{}}
	for i, mode := range modes {
		got := Fold(mode, RoundingModeCases[int]{
			HalfAwayFromZero: func() int { return 0 }, HalfEven: func() int { return 1 },
			TowardZero: func() int { return 2 }, AwayFromZero: func() int { return 3 },
			TowardNegative: func() int { return 4 }, TowardPositive: func() int { return 5 },
		})
		if got != i || !RoundingModeEqual(mode, mode) {
			t.Fatalf("generated enum helper mismatch at %d", i)
		}
		if i > 0 && RoundingModeEqual(mode, modes[0]) {
			t.Fatalf("different modes compare equal at %d", i)
		}
	}
	if !RoundingModeEqual(nil, nil) || RoundingModeEqual(nil, modes[0]) || RoundingModeEqual(invalidRoundingMode{}, invalidRoundingMode{}) {
		t.Fatal("nil/invalid enum equality mismatch")
	}
	overrides := RoundingModeEqOverrides{
		HalfAwayFromZero: func(HalfAwayFromZero, HalfAwayFromZero) (bool, bool) { return false, true },
		HalfEven:         func(HalfEven, HalfEven) (bool, bool) { return true, true },
		TowardZero:       func(TowardZero, TowardZero) (bool, bool) { return true, true },
		AwayFromZero:     func(AwayFromZero, AwayFromZero) (bool, bool) { return true, true },
		TowardNegative:   func(TowardNegative, TowardNegative) (bool, bool) { return true, true },
		TowardPositive:   func(TowardPositive, TowardPositive) (bool, bool) { return true, true },
	}
	if RoundingModeEqualWith(modes[0], modes[0], overrides) || !RoundingModeEqualWith(modes[1], modes[1], overrides) {
		t.Fatal("enum override mismatch")
	}
	if RoundingModeEqual(modes[0], modes[1]) || RoundingModeEqual(modes[1], modes[0]) {
		t.Fatal("first two distinct modes compare equal")
	}
	for _, mode := range modes[2:] {
		if !RoundingModeEqualWith(mode, mode, overrides) {
			t.Fatal("enum handled override mismatch")
		}
	}
	mustPanic(t, func() { Fold(invalidRoundingMode{}, RoundingModeCases[int]{}) })
}

func TestInteropAllInputFormsAndFailures(t *testing.T) {
	d := RequireFromString("12.5")
	text, _ := d.MarshalText()
	if string(text) != "12.5" {
		t.Fatal("MarshalText mismatch")
	}
	for _, input := range []any{int64(-2), uint64(3), float64(1.25)} {
		var got Decimal
		if err := got.Scan(input); err != nil {
			t.Fatal(err)
		}
	}
	var target Decimal
	if err := target.UnmarshalJSON([]byte("null")); err != nil || errString(target.UnmarshalJSON([]byte(`"bad`))) == "" {
		t.Fatal("JSON edge mismatch")
	}
	for _, input := range []any{nil, true, "bad"} {
		if err := target.Scan(input); err == nil {
			t.Fatalf("Scan(%v) succeeded", input)
		}
	}
	if (*Decimal)(nil).UnmarshalText([]byte("1")) == nil || (*Decimal)(nil).UnmarshalJSON([]byte("1")) == nil || (*Decimal)(nil).UnmarshalBinary(nil) == nil || (*Decimal)(nil).Scan("1") == nil {
		t.Fatal("nil Decimal receiver succeeded")
	}
	if target.UnmarshalBinary([]byte{1, 2, 3}) == nil || target.UnmarshalBinary([]byte{0, 0, 0, 0, 0xff}) == nil {
		t.Fatal("invalid binary succeeded")
	}
	binary, _ := d.GobEncode()
	var decoded Decimal
	if err := decoded.GobDecode(binary); err != nil || !decoded.Equal(d) {
		t.Fatal("Gob methods mismatch")
	}
	var viaGob Decimal
	var wireBuffer bytes.Buffer
	if err := gob.NewEncoder(&wireBuffer).Encode(d); err != nil || gob.NewDecoder(&wireBuffer).Decode(&viaGob) != nil || !viaGob.Equal(d) {
		t.Fatal("encoding/gob round trip mismatch")
	}
}

func errString(err error) string {
	if err == nil {
		return ""
	}
	return err.Error()
}

func TestNullDecimalCompleteSurface(t *testing.T) {
	n := NewNullDecimal(One)
	if !n.Valid || !reflect.DeepEqual(n.Decimal, One) {
		t.Fatal("NewNullDecimal mismatch")
	}
	if value, _ := n.Value(); value != "1" {
		t.Fatal("valid Value mismatch")
	}
	if data, _ := n.MarshalJSON(); string(data) != `"1"` {
		t.Fatal("valid JSON mismatch")
	}
	if text, _ := n.MarshalText(); string(text) != "1" {
		t.Fatal("valid text mismatch")
	}
	if text, _ := (NullDecimal{}).MarshalText(); len(text) != 0 {
		t.Fatal("invalid text mismatch")
	}
	for _, input := range [][]byte{[]byte(""), []byte("2.5")} {
		if err := n.UnmarshalText(input); err != nil {
			t.Fatal(err)
		}
	}
	if err := n.UnmarshalText([]byte("bad")); err == nil || n.Valid {
		t.Fatal("invalid text succeeded")
	}
	if err := n.UnmarshalJSON([]byte(`"bad"`)); err == nil || n.Valid {
		t.Fatal("invalid JSON succeeded")
	}
	if err := n.UnmarshalJSON([]byte(`"3"`)); err != nil || !n.Valid {
		t.Fatal("valid JSON failed")
	}
	if err := n.Scan(true); err == nil || n.Valid {
		t.Fatal("invalid scan succeeded")
	}
	if (*NullDecimal)(nil).Scan(nil) == nil || (*NullDecimal)(nil).UnmarshalJSON(nil) == nil || (*NullDecimal)(nil).UnmarshalText(nil) == nil {
		t.Fatal("nil NullDecimal receiver succeeded")
	}
}

func TestFixedCompleteSurfaceAndGuards(t *testing.T) {
	a := Quantize(2, RequireFromString("2.25"), HalfEven{})
	b := Quantize(2, RequireFromString("1.10"), HalfEven{})
	if FixedDecimal(SubFixed(a, b)).String() != "1.15" || FixedDecimal(NegFixed(a)).String() != "-2.25" {
		t.Fatal("fixed subtraction/negation mismatch")
	}
	mustPanic(t, func() { _ = Quantize(-1, One, HalfEven{}) })
	mustPanic(t, func() { _ = RescaleFixed(1000001, a, HalfEven{}) })
	mustPanic(t, func() { _ = SubFixed(a, Quantize(3, One, HalfEven{})) })
	bad := invalidFixed{}
	mustPanic(t, func() { _ = FixedDecimal(bad) })
	mustPanic(t, func() { _ = FixedPlaces(bad) })
	mustPanic(t, func() { _ = AddFixed(bad, a) })
	mustPanic(t, func() { _ = AddFixed(a, bad) })
	mustPanic(t, func() { _ = SubFixed(bad, a) })
	mustPanic(t, func() { _ = SubFixed(a, bad) })
	mustPanic(t, func() { _ = NegFixed(bad) })
	mustPanic(t, func() { _ = MulFixed(bad, a) })
	mustPanic(t, func() { _ = MulFixed(a, bad) })
	mustPanic(t, func() { _ = RescaleFixed(2, bad, HalfEven{}) })
	mustPanic(t, func() { _ = CompareFixed(bad, a) })
	mustPanic(t, func() { _ = CompareFixed(a, bad) })
}

func TestGeneratedBoundaryGuardsAndLongPower(t *testing.T) {
	mustPanic(t, func() { _ = NewFromBigRat(big.NewRat(1, 2), 0) })
	if got := NewFromBigRat(big.NewRat(1, 2), 4).String(); got != "0.5" {
		t.Fatal(got)
	}
	if fromOwned(nil, 0).String() != "0" || pow10(65).BitLen() == 0 {
		t.Fatal("internal fallback mismatch")
	}
	if _, err := parseExponent(math.MaxInt32+1, "large"); err == nil {
		t.Fatal("large parsed exponent succeeded")
	}
	if exponent, err := parseExponent(7, "seven"); err != nil || exponent != 7 {
		t.Fatal("valid parsed exponent failed")
	}
	if got := divisionValue(t, New(1, -10).Divide(One, 2, HalfEven{})).String(); got != "0" {
		t.Fatal("negative shift division mismatch")
	}
	if New(12, 2).IntPart() != 1200 || Max(One, Zero, Ten) != Ten {
		t.Fatal("positive exponent/max mismatch")
	}
	mustPanic(t, func() { _ = Average([]Decimal{One}, 0, HalfEven{}) })
	tooLarge := int32(1000001)
	checks := []func(){
		func() { _ = One.Truncate(tooLarge) }, func() { _ = One.RoundBank(tooLarge) },
		func() { _ = One.RoundDown(tooLarge) }, func() { _ = One.RoundUp(tooLarge) },
		func() { _ = One.RoundFloor(tooLarge) }, func() { _ = One.RoundCeil(tooLarge) },
		func() { _ = One.StringFixed(tooLarge) }, func() { _ = One.StringFixedBank(tooLarge) },
	}
	for _, check := range checks {
		mustPanic(t, check)
	}
}
