package decimal

import (
	"encoding/json"
	"math/big"
	"testing"
	"testing/quick"

	shop "github.com/shopspring/decimal"
)

func TestParseAndStringDifferential(t *testing.T) {
	inputs := []string{"0", "-0", "123", "-123.4500", ".0001", "1.", "+42.5", "1.25e3", "7.50E-2", "999999999999999999999.00001"}
	for _, input := range inputs {
		got, err := NewFromString(input)
		want, upstreamErr := shop.NewFromString(input)
		if (err != nil) != (upstreamErr != nil) {
			t.Fatalf("%q errors differ: got %v, upstream %v", input, err, upstreamErr)
		}
		if err == nil && got.String() != want.String() {
			t.Fatalf("%q = %q, upstream %q", input, got.String(), want.String())
		}
	}
}

func TestArithmeticDifferential(t *testing.T) {
	values := []string{"0", "1", "-1.5", "2.25", "100000000000000000000.01", "0.0000007"}
	for _, as := range values {
		for _, bs := range values {
			a, b := RequireFromString(as), RequireFromString(bs)
			ua, _ := shop.NewFromString(as)
			ub, _ := shop.NewFromString(bs)
			if got, want := a.Add(b).String(), ua.Add(ub).String(); got != want {
				t.Fatalf("%s + %s = %s, upstream %s", as, bs, got, want)
			}
			if got, want := a.Sub(b).String(), ua.Sub(ub).String(); got != want {
				t.Fatalf("%s - %s = %s, upstream %s", as, bs, got, want)
			}
			if got, want := a.Mul(b).String(), ua.Mul(ub).String(); got != want {
				t.Fatalf("%s * %s = %s, upstream %s", as, bs, got, want)
			}
			if got, want := a.Cmp(b), ua.Cmp(ub); got != want {
				t.Fatalf("cmp(%s, %s) = %d, upstream %d", as, bs, got, want)
			}
		}
	}
}

func TestRoundingModes(t *testing.T) {
	tests := []struct {
		input  string
		places int32
		mode   RoundingMode
		want   string
	}{
		{"2.5", 0, HalfAwayFromZero{}, "3"}, {"-2.5", 0, HalfAwayFromZero{}, "-3"},
		{"2.5", 0, HalfEven{}, "2"}, {"3.5", 0, HalfEven{}, "4"},
		{"-2.1", 0, TowardNegative{}, "-3"}, {"-2.9", 0, TowardPositive{}, "-2"},
		{"2.1", 0, AwayFromZero{}, "3"}, {"-2.9", 0, TowardZero{}, "-2"},
	}
	for _, tt := range tests {
		if got := RequireFromString(tt.input).Round(tt.places, tt.mode).String(); got != tt.want {
			t.Errorf("Round(%s) = %s, want %s", tt.input, got, tt.want)
		}
	}
}

func TestRoundingDifferential(t *testing.T) {
	inputs := []string{"-99.995", "-2.500", "-2.499", "-0.001", "0", "0.001", "2.499", "2.500", "99.995", "12345.6789"}
	for _, input := range inputs {
		ours := RequireFromString(input)
		upstream := shop.RequireFromString(input)
		for places := int32(-2); places <= 4; places++ {
			checks := []struct {
				name string
				got  Decimal
				want shop.Decimal
			}{
				{"half-away", ours.Round(places, HalfAwayFromZero{}), upstream.Round(places)},
				{"half-even", ours.Round(places, HalfEven{}), upstream.RoundBank(places)},
				{"toward-zero", ours.Round(places, TowardZero{}), upstream.RoundDown(places)},
				{"away-zero", ours.Round(places, AwayFromZero{}), upstream.RoundUp(places)},
				{"floor", ours.Round(places, TowardNegative{}), upstream.RoundFloor(places)},
				{"ceiling", ours.Round(places, TowardPositive{}), upstream.RoundCeil(places)},
			}
			for _, check := range checks {
				if got, want := check.got.String(), check.want.String(); got != want {
					t.Fatalf("%s Round(%s, %d) = %s, upstream %s", check.name, input, places, got, want)
				}
			}
		}
	}
}

func TestStringFixedDifferential(t *testing.T) {
	inputs := []string{"0", "1", "-1.25", "2.345", "999999999999999.995", "0.00001"}
	for _, input := range inputs {
		for places := int32(0); places <= 6; places++ {
			got := RequireFromString(input).StringFixed(places)
			upstream := shop.RequireFromString(input).StringFixed(places)
			if got != upstream {
				t.Fatalf("StringFixed(%s, %d) = %q, upstream %q", input, places, got, upstream)
			}
			if got, want := RequireFromString(input).StringFixedBank(places), shop.RequireFromString(input).StringFixedBank(places); got != want {
				t.Fatalf("StringFixedBank(%s, %d) = %q, upstream %q", input, places, got, want)
			}
		}
	}
}

func TestCompatibilityHelpersDifferential(t *testing.T) {
	inputs := []string{"-100.25", "-1", "0", "0.001", "1.2300", "999999999999999999.9"}
	for _, input := range inputs {
		got := RequireFromString(input)
		want := shop.RequireFromString(input)
		if got.IsInteger() != want.IsInteger() {
			t.Fatalf("IsInteger(%s) differs", input)
		}
		if got.BigInt().Cmp(want.BigInt()) != 0 {
			t.Fatalf("BigInt(%s) differs", input)
		}
		if got.Rat().Cmp(want.Rat()) != 0 {
			t.Fatalf("Rat(%s) differs", input)
		}
		if got.CoefficientInt64() != want.CoefficientInt64() {
			t.Fatalf("CoefficientInt64(%s) differs", input)
		}
	}
	a, b := RequireFromString("5.5"), RequireFromString("2")
	ua, ub := shop.RequireFromString("5.5"), shop.RequireFromString("2")
	if got, want := a.Mod(b).String(), ua.Mod(ub).String(); got != want {
		t.Fatalf("Mod = %s, upstream %s", got, want)
	}
	if Sum(a, b).String() != shop.Sum(ua, ub).String() {
		t.Fatal("Sum differs")
	}
	if Min(a, b).String() != shop.Min(ua, ub).String() || Max(a, b).String() != shop.Max(ua, ub).String() {
		t.Fatal("Min/Max differ")
	}
}

func TestFloatAndRatConversions(t *testing.T) {
	for _, input := range []float64{0, -0.5, 0.1, 1.25, 1e20, 1e-20} {
		got, err := NewFromFloat(input)
		if err != nil {
			t.Fatal(err)
		}
		want := shop.NewFromFloat(input)
		if got.String() != want.String() {
			t.Fatalf("NewFromFloat(%g) = %s, upstream %s", input, got.String(), want.String())
		}
		converted, _ := got.Float64()
		if converted != input {
			t.Fatalf("Float64(%s) = %.20g, want %.20g", got.String(), converted, input)
		}
	}
	if got := NewFromBigRat(big.NewRat(2, 3), 4).String(); got != "0.6667" {
		t.Fatalf("2/3 = %s", got)
	}
}

func TestDivideOutcome(t *testing.T) {
	describe := func(result DivisionResult) string {
		switch value := result.(type) {
		case Exact:
			return "exact:" + value.Value.String()
		case Rounded:
			return "rounded:" + value.Value.String()
		case DivisionByZero:
			return "zero"
		default:
			return "invalid"
		}
	}
	if got := describe(NewFromInt(1).Divide(NewFromInt(4), 3, HalfEven{})); got != "exact:0.25" {
		t.Fatal(got)
	}
	if got := describe(NewFromInt(1).Divide(NewFromInt(3), 2, HalfAwayFromZero{})); got != "rounded:0.33" {
		t.Fatal(got)
	}
	if got := describe(NewFromInt(1).Divide(Zero, 2, HalfEven{})); got != "zero" {
		t.Fatal(got)
	}
	if got := describe(NewFromInt(1).Divide(NewFromInt(-8), 2, TowardNegative{})); got != "rounded:-0.13" {
		t.Fatal(got)
	}
}

func divisionValue(t *testing.T, result DivisionResult) Decimal {
	t.Helper()
	switch value := result.(type) {
	case Exact:
		return value.Value
	case Rounded:
		return value.Value
	case DivisionByZero:
		t.Fatal("unexpected division by zero")
	default:
		t.Fatal("invalid division result")
	}
	return Zero
}

func TestDivisionDifferential(t *testing.T) {
	pairs := [][2]string{{"1", "3"}, {"2", "7"}, {"-10", "6"}, {"10", "-6"}, {"1.25", "0.04"}, {"100000000000000000001", "9"}}
	for _, pair := range pairs {
		oursLeft, oursRight := RequireFromString(pair[0]), RequireFromString(pair[1])
		upLeft, upRight := shop.RequireFromString(pair[0]), shop.RequireFromString(pair[1])
		for precision := int32(1); precision <= 8; precision++ {
			got := divisionValue(t, oursLeft.Divide(oursRight, precision, HalfAwayFromZero{})).String()
			want := upLeft.DivRound(upRight, precision).String()
			if got != want {
				t.Fatalf("%s/%s precision %d = %s, upstream %s", pair[0], pair[1], precision, got, want)
			}
		}
	}
}

func TestAverageUsesExplicitPolicy(t *testing.T) {
	result := Average([]Decimal{One, One, Zero}, 2, HalfAwayFromZero{})
	if got := divisionValue(t, result).String(); got != "0.67" {
		t.Fatalf("Average = %s", got)
	}
	if _, ok := Average(nil, 2, HalfEven{}).(DivisionByZero); !ok {
		t.Fatal("empty Average did not report DivisionByZero")
	}
}

func TestImmutabilityAndZeroValue(t *testing.T) {
	coefficient := big.NewInt(123)
	d := NewFromBigInt(coefficient, -2)
	coefficient.SetInt64(999)
	d.Coefficient().SetInt64(777)
	if d.String() != "1.23" {
		t.Fatalf("mutation escaped: %s", d.String())
	}
	var zero Decimal
	if zero.String() != "0" || !zero.Equal(Zero) {
		t.Fatalf("zero value = %s", zero.String())
	}
}

func TestSerialization(t *testing.T) {
	want := RequireFromString("-12345678901234567890.004500")
	data, err := json.Marshal(want)
	if err != nil {
		t.Fatal(err)
	}
	if string(data) != `"-12345678901234567890.0045"` {
		t.Fatalf("JSON = %s", data)
	}
	var decoded Decimal
	if err := json.Unmarshal(data, &decoded); err != nil {
		t.Fatal(err)
	}
	if !decoded.Equal(want) {
		t.Fatalf("JSON round trip = %s", decoded.String())
	}
	binaryValue, err := want.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	if err := decoded.UnmarshalBinary(binaryValue); err != nil {
		t.Fatal(err)
	}
	if decoded.Exponent() != want.Exponent() || decoded.Coefficient().Cmp(want.Coefficient()) != 0 {
		t.Fatal("binary did not preserve representation")
	}
	upstream, _ := shop.NewFromString("-12345678901234567890.004500")
	upstreamBinary, err := upstream.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	if string(binaryValue) != string(upstreamBinary) {
		t.Fatal("binary encoding differs from shopspring/decimal")
	}
}

func TestDatabaseInterfaces(t *testing.T) {
	want := RequireFromString("12345678901234567890.125")
	value, err := want.Value()
	if err != nil || value != want.String() {
		t.Fatalf("Value = %v, %v", value, err)
	}
	for _, input := range []any{want.String(), []byte(want.String())} {
		var got Decimal
		if err := got.Scan(input); err != nil {
			t.Fatal(err)
		}
		if !got.Equal(want) {
			t.Fatalf("Scan(%T) = %s", input, got.String())
		}
	}
}

func TestNullDecimal(t *testing.T) {
	var value NullDecimal
	if err := value.Scan(nil); err != nil || value.Valid {
		t.Fatalf("Scan(nil) = %+v, %v", value, err)
	}
	if sqlValue, err := value.Value(); err != nil || sqlValue != nil {
		t.Fatalf("Value = %v, %v", sqlValue, err)
	}
	data, err := json.Marshal(value)
	if err != nil || string(data) != "null" {
		t.Fatalf("MarshalJSON = %s, %v", data, err)
	}
	if err := value.Scan("12.30"); err != nil || !value.Valid || value.Decimal.String() != "12.3" {
		t.Fatalf("Scan = %+v, %v", value, err)
	}
	if err := json.Unmarshal([]byte("null"), &value); err != nil || value.Valid {
		t.Fatalf("Unmarshal null = %+v, %v", value, err)
	}
}

func TestAdditiveAndMultiplicativeLaws(t *testing.T) {
	check := func(a, b, c int32) bool {
		x, y, z := New(int64(a), -2), New(int64(b), -2), New(int64(c), -2)
		return x.Add(y).Equal(y.Add(x)) &&
			x.Add(y).Add(z).Equal(x.Add(y.Add(z))) &&
			x.Add(Zero).Equal(x) &&
			x.Mul(One).Equal(x) &&
			x.Mul(y.Add(z)).Equal(x.Mul(y).Add(x.Mul(z)))
	}
	if err := quick.Check(check, &quick.Config{MaxCount: 1000}); err != nil {
		t.Fatal(err)
	}
}

func TestPlainGoPrecisionGuard(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("Divide accepted zero Precision from plain Go")
		}
	}()
	_ = One.Divide(Ten, 0, HalfEven{})
}

func TestPlainGoScaleGuard(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("Round accepted an unbounded Scale from plain Go")
		}
	}()
	_ = One.Round(1000001, HalfEven{})
}

func TestFixedRuntimeAPI(t *testing.T) {
	a := Quantize(2, RequireFromString("1.234"), HalfAwayFromZero{})
	b := Quantize(2, RequireFromString("2.345"), HalfAwayFromZero{})
	if got := FixedDecimal(AddFixed(a, b)).String(); got != "3.58" {
		t.Fatalf("fixed sum = %s", got)
	}
	product := MulFixed(a, RescaleFixed(3, b, HalfEven{}))
	if FixedPlaces(product) != 5 {
		t.Fatalf("product scale = %d", FixedPlaces(product))
	}
	if got := FixedDecimal(product).String(); got != "2.8905" {
		t.Fatalf("fixed product = %s", got)
	}
	if CompareFixed(a, b) >= 0 {
		t.Fatal("CompareFixed lost numeric ordering")
	}
}

func TestPlainGoFixedScaleGuard(t *testing.T) {
	a := Quantize(2, One, HalfEven{})
	b := Quantize(3, One, HalfEven{})
	defer func() {
		if recover() == nil {
			t.Fatal("AddFixed accepted unequal runtime scales from plain Go")
		}
	}()
	_ = AddFixed(a, b)
}

func FuzzParseRoundTrip(f *testing.F) {
	for _, seed := range []string{"0", "-1.25", ".5", "1e20", "not-a-number"} {
		f.Add(seed)
	}
	f.Fuzz(func(t *testing.T, input string) {
		d, err := NewFromString(input)
		if err != nil {
			return
		}
		roundTrip, err := NewFromString(d.String())
		if err != nil || !roundTrip.Equal(d) {
			t.Fatalf("%q -> %q -> %v (%v)", input, d.String(), roundTrip, err)
		}
	})
}

func FuzzParseDifferential(f *testing.F) {
	for _, seed := range []string{"0", "-1.25", "+1.0", ".5", "1.", "1e20", "1E-20", "NaN", "not-a-number"} {
		f.Add(seed)
	}
	f.Fuzz(func(t *testing.T, input string) {
		got, gotErr := NewFromString(input)
		want, wantErr := shop.NewFromString(input)
		// Go+ deliberately accepts a stricter conventional grammar; for
		// example, Shopspring accepts a sign after a leading decimal point.
		if gotErr != nil {
			return
		}
		if wantErr != nil {
			t.Fatalf("%q accepted by ours but rejected upstream: %v", input, wantErr)
		}
		if got.String() != want.String() {
			t.Fatalf("%q = %q, upstream %q", input, got.String(), want.String())
		}
	})
}

func FuzzArithmeticDifferential(f *testing.F) {
	f.Add(int64(123), int8(-2), int64(-45), int8(3))
	f.Add(int64(0), int8(0), int64(1), int8(-8))
	f.Fuzz(func(t *testing.T, ac int64, ae int8, bc int64, be int8) {
		a, b := New(ac, int32(ae)), New(bc, int32(be))
		ua, ub := shop.New(ac, int32(ae)), shop.New(bc, int32(be))
		checks := []struct{ name, got, want string }{
			{"add", a.Add(b).String(), ua.Add(ub).String()},
			{"sub", a.Sub(b).String(), ua.Sub(ub).String()},
			{"mul", a.Mul(b).String(), ua.Mul(ub).String()},
		}
		for _, check := range checks {
			if check.got != check.want {
				t.Fatalf("%s differs: ours=%s upstream=%s", check.name, check.got, check.want)
			}
		}
		if a.Cmp(b) != ua.Cmp(ub) {
			t.Fatalf("Cmp differs for %v and %v", a, b)
		}
	})
}

func BenchmarkAdd(b *testing.B) {
	x := RequireFromString("12345678901234567890.12345")
	y := RequireFromString("0.00000000000000000000009")
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		_ = x.Add(y)
	}
}

func BenchmarkAddUpstream(b *testing.B) {
	x := shop.RequireFromString("12345678901234567890.12345")
	y := shop.RequireFromString("0.00000000000000000000009")
	b.ReportAllocs()
	for i := 0; i < b.N; i++ {
		_ = x.Add(y)
	}
}

func TestAddAllocationBudget(t *testing.T) {
	x := RequireFromString("12345678901234567890.12345")
	y := RequireFromString("0.00000000000000000000009")
	allocations := testing.AllocsPerRun(1000, func() { _ = x.Add(y) })
	if allocations > 4 {
		t.Fatalf("Add allocations = %.1f, budget 4", allocations)
	}
}
