package smt

import "testing"

func TestFloatingPointGroundClassification(t *testing.T) {
	tests := []struct {
		name                                  string
		bits                                  uint64
		nan, infinite, zero                   bool
		subnormal, normal, negative, positive bool
	}{
		{name: "positive zero", bits: 0x00000000, zero: true, positive: true},
		{name: "negative zero", bits: 0x80000000, zero: true, negative: true},
		{name: "positive infinity", bits: 0x7f800000, infinite: true, positive: true},
		{name: "negative infinity", bits: 0xff800000, infinite: true, negative: true},
		{name: "quiet NaN", bits: 0x7fc00000, nan: true},
		{name: "negative NaN", bits: 0xffc00000, nan: true},
		{name: "least subnormal", bits: 0x00000001, subnormal: true, positive: true},
		{name: "one", bits: 0x3f800000, normal: true, positive: true},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			value := FloatingPointFromUint64(8, 24, test.bits)
			if got := FloatingPointIsNaN(value); got != test.nan {
				t.Fatalf("isNaN = %v, want %v", got, test.nan)
			}
			if got := FloatingPointIsInfinite(value); got != test.infinite {
				t.Fatalf("isInfinite = %v, want %v", got, test.infinite)
			}
			if got := FloatingPointIsZero(value); got != test.zero {
				t.Fatalf("isZero = %v, want %v", got, test.zero)
			}
			if got := FloatingPointIsSubnormal(value); got != test.subnormal {
				t.Fatalf("isSubnormal = %v, want %v", got, test.subnormal)
			}
			if got := FloatingPointIsNormal(value); got != test.normal {
				t.Fatalf("isNormal = %v, want %v", got, test.normal)
			}
			if got := FloatingPointIsNegative(value); got != test.negative {
				t.Fatalf("isNegative = %v, want %v", got, test.negative)
			}
			if got := FloatingPointIsPositive(value); got != test.positive {
				t.Fatalf("isPositive = %v, want %v", got, test.positive)
			}
			bits, ok := FloatingPointBits(value).Uint64()
			if !ok || bits != test.bits {
				t.Fatalf("round trip = %#x, %v; want %#x, true", bits, ok, test.bits)
			}
		})
	}
}

func TestFloatingPointGroundEquality(t *testing.T) {
	positiveZero := FloatingPointFromUint64(8, 24, 0x00000000)
	negativeZero := FloatingPointFromUint64(8, 24, 0x80000000)
	one := FloatingPointFromUint64(8, 24, 0x3f800000)
	nan := FloatingPointFromUint64(8, 24, 0x7fc00000)
	if !FloatingPointEqual(positiveZero, negativeZero) {
		t.Fatal("fp.eq must equate signed zeros")
	}
	if !FloatingPointEqual(one, one) {
		t.Fatal("fp.eq must equate identical ordinary values")
	}
	if FloatingPointEqual(nan, nan) {
		t.Fatal("fp.eq must not equate NaN with itself")
	}
}

func TestFloatingPointGroundAbsAndNeg(t *testing.T) {
	tests := []struct {
		name string
		bits uint64
		abs  uint64
		neg  uint64
	}{
		{"positive zero", 0x00000000, 0x00000000, 0x80000000},
		{"negative zero", 0x80000000, 0x00000000, 0x00000000},
		{"positive normal", 0x3f800000, 0x3f800000, 0xbf800000},
		{"negative normal", 0xbf800000, 0x3f800000, 0x3f800000},
		{"positive infinity", 0x7f800000, 0x7f800000, 0xff800000},
		{"negative NaN payload", 0xffc12345, 0x7fc12345, 0x7fc12345},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			value := FloatingPointFromUint64(8, 24, test.bits)
			absolute, ok := FloatingPointBits(FloatingPointAbs(value)).Uint64()
			if !ok || absolute != test.abs {
				t.Fatalf("abs bits = %#x, want %#x", absolute, test.abs)
			}
			negated, ok := FloatingPointBits(FloatingPointNeg(value)).Uint64()
			if !ok || negated != test.neg {
				t.Fatalf("neg bits = %#x, want %#x", negated, test.neg)
			}
		})
	}
}

func TestFloatingPointArbitraryFormatAbsAndNeg(t *testing.T) {
	bits, err := ParseBitVector(128, "0x80000000000000000000000000000001")
	if err != nil {
		t.Fatal(err)
	}
	value := FloatingPointFromBits(15, 113, bits)
	absolute := FloatingPointBits(FloatingPointAbs(value))
	negated := FloatingPointBits(FloatingPointNeg(value))
	if absolute.Bit(127) || !absolute.Bit(0) {
		t.Fatalf("unexpected binary128 absolute value: %v", absolute)
	}
	if negated.Bit(127) || !negated.Bit(0) {
		t.Fatalf("unexpected binary128 negated value: %v", negated)
	}
}

func TestFloatingPointArbitraryFormat(t *testing.T) {
	bits, err := ParseBitVector(128, "0x7fff0000000000000000000000000000")
	if err != nil {
		t.Fatal(err)
	}
	infinity := FloatingPointFromBits(15, 113, bits)
	if !FloatingPointIsInfinite(infinity) || !FloatingPointIsPositive(infinity) {
		t.Fatal("binary128 positive infinity was not classified exactly")
	}
	if !EqualBitVectorValue(FloatingPointBits(infinity), bits) {
		t.Fatal("binary128 bit pattern did not round trip")
	}
}

func TestFloatingPointGroundValidation(t *testing.T) {
	for _, test := range []struct {
		name string
		run  func()
	}{
		{"small exponent", func() { FloatingPointFromUint64(1, 24, 0) }},
		{"small significand", func() { FloatingPointFromUint64(8, 1, 0) }},
		{"wrong bit width", func() { FloatingPointFromBits(8, 24, NewBitVectorUint64(31, 0)) }},
	} {
		t.Run(test.name, func(t *testing.T) {
			defer func() {
				if recover() == nil {
					t.Fatal("expected panic")
				}
			}()
			test.run()
		})
	}
}
