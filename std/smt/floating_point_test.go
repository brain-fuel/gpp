package smt

import (
	"math/big"
	"testing"
)

func floatingPointTestBits64(t *testing.T, value FloatingPointValue) uint64 {
	t.Helper()
	bits, inline := FloatingPointBits(value).Uint64()
	if !inline {
		t.Fatal("expected inline floating-point value")
	}
	return bits
}

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

func TestFloatingPointComponentsAndSpecialValues(t *testing.T) {
	one := FloatingPointFromComponents(
		8, 24,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(8, 0x7f),
		NewBitVectorUint64(23, 0),
	)
	bits, ok := FloatingPointBits(one).Uint64()
	if !ok || bits != 0x3f800000 {
		t.Fatalf("component bits=%#x,%v, want 0x3f800000,true", bits, ok)
	}
	cases := []struct {
		name  string
		value FloatingPointValue
		bits  uint64
	}{
		{"+zero", FloatingPointPositiveZero(8, 24), 0x00000000},
		{"-zero", FloatingPointNegativeZero(8, 24), 0x80000000},
		{"+oo", FloatingPointPositiveInfinity(8, 24), 0x7f800000},
		{"-oo", FloatingPointNegativeInfinity(8, 24), 0xff800000},
		{"NaN", FloatingPointNaN(8, 24), 0x7fc00000},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			got, ok := FloatingPointBits(test.value).Uint64()
			if !ok || got != test.bits {
				t.Fatalf("bits=%#x,%v, want %#x,true", got, ok, test.bits)
			}
		})
	}
	binary128Infinity := FloatingPointPositiveInfinity(15, 113)
	if bits := FloatingPointBits(binary128Infinity); bits.Width() != 128 ||
		!FloatingPointIsInfinite(binary128Infinity) {
		t.Fatalf("binary128 infinity bits=%v", bits)
	}
	binary128NaN := FloatingPointNaN(15, 113)
	if bits := FloatingPointBits(binary128NaN); bits.Width() != 128 ||
		!FloatingPointIsNaN(binary128NaN) {
		t.Fatalf("binary128 NaN bits=%v", bits)
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

func TestFloatingPointGroundOrdering(t *testing.T) {
	values := []struct {
		name string
		bits uint64
	}{
		{"negative infinity", 0xff800000},
		{"negative one", 0xbf800000},
		{"negative zero", 0x80000000},
		{"positive zero", 0x00000000},
		{"positive one", 0x3f800000},
		{"positive infinity", 0x7f800000},
	}
	for leftIndex, leftCase := range values {
		for rightIndex, rightCase := range values {
			left := FloatingPointFromUint64(8, 24, leftCase.bits)
			right := FloatingPointFromUint64(8, 24, rightCase.bits)
			equalZeros := leftIndex == 2 && rightIndex == 3 || leftIndex == 3 && rightIndex == 2
			wantLess := leftIndex < rightIndex && !equalZeros
			wantEqual := leftIndex == rightIndex || equalZeros
			if got := FloatingPointLessThan(left, right); got != wantLess {
				t.Fatalf("%s < %s = %v, want %v", leftCase.name, rightCase.name, got, wantLess)
			}
			if got := FloatingPointLessOrEqual(left, right); got != (wantLess || wantEqual) {
				t.Fatalf("%s <= %s = %v, want %v", leftCase.name, rightCase.name, got, wantLess || wantEqual)
			}
			if got := FloatingPointGreaterThan(left, right); got != FloatingPointLessThan(right, left) {
				t.Fatalf("%s > %s = %v", leftCase.name, rightCase.name, got)
			}
			if got := FloatingPointGreaterOrEqual(left, right); got != FloatingPointLessOrEqual(right, left) {
				t.Fatalf("%s >= %s = %v", leftCase.name, rightCase.name, got)
			}
		}
	}
	nan := FloatingPointFromUint64(8, 24, 0x7fc00000)
	one := FloatingPointFromUint64(8, 24, 0x3f800000)
	if FloatingPointLessThan(nan, one) || FloatingPointLessOrEqual(nan, one) ||
		FloatingPointGreaterThan(nan, one) || FloatingPointGreaterOrEqual(nan, one) {
		t.Fatal("NaN must be unordered")
	}
}

func TestFloatingPointGroundMinMax(t *testing.T) {
	negativeOne := FloatingPointFromUint64(8, 24, 0xbf800000)
	positiveOne := FloatingPointFromUint64(8, 24, 0x3f800000)
	nan := FloatingPointFromUint64(8, 24, 0x7fc12345)
	if !FloatingPointEqual(FloatingPointMin(negativeOne, positiveOne), negativeOne) {
		t.Fatal("min(-1,+1) must be -1")
	}
	if !FloatingPointEqual(FloatingPointMax(negativeOne, positiveOne), positiveOne) {
		t.Fatal("max(-1,+1) must be +1")
	}
	if !FloatingPointEqual(FloatingPointMin(nan, positiveOne), positiveOne) ||
		!FloatingPointEqual(FloatingPointMax(positiveOne, nan), positiveOne) {
		t.Fatal("a sole NaN must yield the numeric operand")
	}
	leftNaN := FloatingPointFromUint64(8, 24, 0x7fc12345)
	rightNaN := FloatingPointFromUint64(8, 24, 0xffc54321)
	if !EqualBitVectorValue(
		FloatingPointBits(FloatingPointMin(leftNaN, rightNaN)),
		FloatingPointBits(rightNaN),
	) {
		t.Fatal("deterministic two-NaN min must select the right payload")
	}
}

func TestFloatingPointRoundToIntegralModes(t *testing.T) {
	tests := []struct {
		name string
		mode FloatingPointRoundingMode
		bits uint64
		want uint64
	}{
		{"RNE tie odd", RoundNearestTiesToEven(), 0x3fc00000, 0x40000000},
		{"RNE tie even", RoundNearestTiesToEven(), 0x40200000, 0x40000000},
		{"RNA tie", RoundNearestTiesToAway(), 0x40200000, 0x40400000},
		{"RTP positive", RoundTowardPositive(), 0x3fa00000, 0x40000000},
		{"RTP negative", RoundTowardPositive(), 0xbfa00000, 0xbf800000},
		{"RTN positive", RoundTowardNegative(), 0x3fa00000, 0x3f800000},
		{"RTN negative", RoundTowardNegative(), 0xbfa00000, 0xc0000000},
		{"RTZ positive", RoundTowardZero(), 0x3fa00000, 0x3f800000},
		{"RTZ negative", RoundTowardZero(), 0xbfa00000, 0xbf800000},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			value := FloatingPointFromUint64(8, 24, test.bits)
			rounded := FloatingPointRoundToIntegral(test.mode, value)
			got, ok := FloatingPointBits(rounded).Uint64()
			if !ok || got != test.want {
				t.Fatalf("bits=%#x, want %#x", got, test.want)
			}
		})
	}
}

func TestFloatingPointRoundToIntegralBinary128(t *testing.T) {
	bits, err := ParseBitVector(
		128, "0x3fff8000000000000000000000000000",
	)
	if err != nil {
		t.Fatal(err)
	}
	value := FloatingPointFromBits(15, 113, bits)
	rounded := FloatingPointRoundToIntegral(RoundNearestTiesToEven(), value)
	want, err := ParseBitVector(
		128, "0x40000000000000000000000000000000",
	)
	if err != nil {
		t.Fatal(err)
	}
	if !EqualBitVectorValue(FloatingPointBits(rounded), want) {
		t.Fatalf("binary128 rounded bits=%v, want %v", FloatingPointBits(rounded), want)
	}
}

func TestFloatingPointAddBinary32(t *testing.T) {
	modes := []struct {
		name string
		mode FloatingPointRoundingMode
	}{
		{"RNE", RoundNearestTiesToEven()},
		{"RNA", RoundNearestTiesToAway()},
		{"RTP", RoundTowardPositive()},
		{"RTN", RoundTowardNegative()},
		{"RTZ", RoundTowardZero()},
	}
	tests := []struct {
		name        string
		left, right uint64
		want        [5]uint64
	}{
		{"exact", 0x3f800000, 0x3f800000, [5]uint64{0x40000000, 0x40000000, 0x40000000, 0x40000000, 0x40000000}},
		{"positive tie", 0x3f800000, 0x33800000, [5]uint64{0x3f800000, 0x3f800001, 0x3f800001, 0x3f800000, 0x3f800000}},
		{"negative tie", 0xbf800000, 0xb3800000, [5]uint64{0xbf800000, 0xbf800001, 0xbf800000, 0xbf800001, 0xbf800000}},
		{"cancellation", 0x3f800000, 0xbf800000, [5]uint64{0, 0, 0, 0x80000000, 0}},
		{"subnormal carry", 0x007fffff, 0x00000001, [5]uint64{0x00800000, 0x00800000, 0x00800000, 0x00800000, 0x00800000}},
		{"positive dominance", 0x3f800000, 0x00000001, [5]uint64{0x3f800000, 0x3f800000, 0x3f800001, 0x3f800000, 0x3f800000}},
		{"opposite dominance", 0x3f800000, 0x80000001, [5]uint64{0x3f800000, 0x3f800000, 0x3f800000, 0x3f7fffff, 0x3f7fffff}},
		{"overflow", 0x7f7fffff, 0x7f7fffff, [5]uint64{0x7f800000, 0x7f800000, 0x7f800000, 0x7f7fffff, 0x7f7fffff}},
		{"negative overflow", 0xff7fffff, 0xff7fffff, [5]uint64{0xff800000, 0xff800000, 0xff7fffff, 0xff800000, 0xff7fffff}},
	}
	for _, test := range tests {
		for modeIndex, mode := range modes {
			t.Run(test.name+"/"+mode.name, func(t *testing.T) {
				sum := FloatingPointAdd(
					mode.mode,
					FloatingPointFromUint64(8, 24, test.left),
					FloatingPointFromUint64(8, 24, test.right),
				)
				got, ok := FloatingPointBits(sum).Uint64()
				if !ok || got != test.want[modeIndex] {
					t.Fatalf("bits=%#08x,%v, want %#08x,true", got, ok, test.want[modeIndex])
				}
			})
		}
	}
}

func TestFloatingPointAddSpecialValues(t *testing.T) {
	positiveInfinity := FloatingPointPositiveInfinity(8, 24)
	negativeInfinity := FloatingPointNegativeInfinity(8, 24)
	one := FloatingPointFromUint64(8, 24, 0x3f800000)
	nan := FloatingPointNaN(8, 24)
	if !FloatingPointIsInfinite(FloatingPointAdd(RoundNearestTiesToEven(), positiveInfinity, one)) {
		t.Fatal("positive infinity plus finite must be infinite")
	}
	if !FloatingPointIsNaN(FloatingPointAdd(RoundNearestTiesToEven(), positiveInfinity, negativeInfinity)) {
		t.Fatal("opposite infinities must produce NaN")
	}
	if !FloatingPointIsNaN(FloatingPointAdd(RoundNearestTiesToEven(), nan, one)) {
		t.Fatal("NaN addition must produce NaN")
	}
	negativeZero := FloatingPointAdd(
		RoundTowardNegative(),
		FloatingPointPositiveZero(8, 24),
		FloatingPointNegativeZero(8, 24),
	)
	bits, _ := FloatingPointBits(negativeZero).Uint64()
	if bits != 0x80000000 {
		t.Fatalf("mixed zero under RTN=%#08x, want negative zero", bits)
	}
}

func TestFloatingPointAddBinary128Tie(t *testing.T) {
	one := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x3fff),
		NewBitVectorUint64(112, 0),
	)
	halfULP := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x3fff-113),
		NewBitVectorUint64(112, 0),
	)
	even := FloatingPointAdd(RoundNearestTiesToEven(), one, halfULP)
	if !EqualBitVectorValue(FloatingPointBits(even), FloatingPointBits(one)) {
		t.Fatalf("binary128 RNE tie=%v, want one", FloatingPointBits(even))
	}
	away := FloatingPointAdd(RoundNearestTiesToAway(), one, halfULP)
	wantAway := AddBitVectorValue(
		FloatingPointBits(one), NewBitVectorUint64(128, 1),
	)
	if !EqualBitVectorValue(FloatingPointBits(away), wantAway) {
		t.Fatalf("binary128 RNA tie=%v, want %v", FloatingPointBits(away), wantAway)
	}
	subAway := FloatingPointSub(
		RoundNearestTiesToAway(), one, FloatingPointNeg(halfULP),
	)
	if !EqualBitVectorValue(FloatingPointBits(subAway), wantAway) {
		t.Fatalf("binary128 fp.sub RNA tie=%v, want %v", FloatingPointBits(subAway), wantAway)
	}
	two := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x4000),
		NewBitVectorUint64(112, 0),
	)
	product := FloatingPointMul(RoundNearestTiesToEven(), one, two)
	if !EqualBitVectorValue(FloatingPointBits(product), FloatingPointBits(two)) {
		t.Fatalf("binary128 fp.mul=%v, want %v", FloatingPointBits(product), FloatingPointBits(two))
	}
}

func TestFloatingPointSubBinary32(t *testing.T) {
	modes := []FloatingPointRoundingMode{
		RoundNearestTiesToEven(),
		RoundNearestTiesToAway(),
		RoundTowardPositive(),
		RoundTowardNegative(),
		RoundTowardZero(),
	}
	tests := []struct {
		name        string
		left, right uint64
		want        [5]uint64
	}{
		{"exact", 0x40700000, 0x40100000, [5]uint64{0x3fc00000, 0x3fc00000, 0x3fc00000, 0x3fc00000, 0x3fc00000}},
		{"positive tie", 0x3f800000, 0xb3800000, [5]uint64{0x3f800000, 0x3f800001, 0x3f800001, 0x3f800000, 0x3f800000}},
		{"cancellation", 0x3f800000, 0x3f800000, [5]uint64{0, 0, 0, 0x80000000, 0}},
		{"subnormal borrow", 0x00800000, 0x00000001, [5]uint64{0x007fffff, 0x007fffff, 0x007fffff, 0x007fffff, 0x007fffff}},
		{"dominance", 0x3f800000, 0x00000001, [5]uint64{0x3f800000, 0x3f800000, 0x3f800000, 0x3f7fffff, 0x3f7fffff}},
		{"overflow", 0x7f7fffff, 0xff7fffff, [5]uint64{0x7f800000, 0x7f800000, 0x7f800000, 0x7f7fffff, 0x7f7fffff}},
	}
	for _, test := range tests {
		for modeIndex, mode := range modes {
			difference := FloatingPointSub(
				mode,
				FloatingPointFromUint64(8, 24, test.left),
				FloatingPointFromUint64(8, 24, test.right),
			)
			got, ok := FloatingPointBits(difference).Uint64()
			if !ok || got != test.want[modeIndex] {
				t.Fatalf("%s mode %d bits=%#08x,%v, want %#08x,true", test.name, modeIndex, got, ok, test.want[modeIndex])
			}
		}
	}
}

func TestFloatingPointSubSpecialValues(t *testing.T) {
	positiveInfinity := FloatingPointPositiveInfinity(8, 24)
	negativeInfinity := FloatingPointNegativeInfinity(8, 24)
	if !FloatingPointIsNaN(FloatingPointSub(
		RoundNearestTiesToEven(), positiveInfinity, positiveInfinity,
	)) {
		t.Fatal("infinity minus itself must produce NaN")
	}
	if difference := FloatingPointSub(
		RoundNearestTiesToEven(), positiveInfinity, negativeInfinity,
	); !FloatingPointIsInfinite(difference) || FloatingPointIsNegative(difference) {
		t.Fatal("positive infinity minus negative infinity must be positive infinity")
	}
}

func TestFloatingPointMulBinary32(t *testing.T) {
	modes := []FloatingPointRoundingMode{
		RoundNearestTiesToEven(),
		RoundNearestTiesToAway(),
		RoundTowardPositive(),
		RoundTowardNegative(),
		RoundTowardZero(),
	}
	tests := []struct {
		name        string
		left, right uint64
		want        [5]uint64
	}{
		{"exact", 0x3fc00000, 0x40100000, [5]uint64{0x40580000, 0x40580000, 0x40580000, 0x40580000, 0x40580000}},
		{"subnormal exact", 0x00800000, 0x3f000000, [5]uint64{0x00400000, 0x00400000, 0x00400000, 0x00400000, 0x00400000}},
		{"positive underflow tie", 0x00000001, 0x3f000000, [5]uint64{0, 1, 1, 0, 0}},
		{"negative underflow tie", 0x80000001, 0x3f000000, [5]uint64{0x80000000, 0x80000001, 0x80000000, 0x80000001, 0x80000000}},
		{"overflow", 0x7f7fffff, 0x40000000, [5]uint64{0x7f800000, 0x7f800000, 0x7f800000, 0x7f7fffff, 0x7f7fffff}},
	}
	for _, test := range tests {
		for modeIndex, mode := range modes {
			product := FloatingPointMul(
				mode,
				FloatingPointFromUint64(8, 24, test.left),
				FloatingPointFromUint64(8, 24, test.right),
			)
			got, ok := FloatingPointBits(product).Uint64()
			if !ok || got != test.want[modeIndex] {
				t.Fatalf("%s mode %d bits=%#08x,%v, want %#08x,true", test.name, modeIndex, got, ok, test.want[modeIndex])
			}
		}
	}
}

func TestFloatingPointMulSpecialValues(t *testing.T) {
	positiveInfinity := FloatingPointPositiveInfinity(8, 24)
	negativeZero := FloatingPointNegativeZero(8, 24)
	if !FloatingPointIsNaN(FloatingPointMul(
		RoundNearestTiesToEven(), positiveInfinity, negativeZero,
	)) {
		t.Fatal("infinity times zero must produce NaN")
	}
	negative := FloatingPointMul(
		RoundNearestTiesToEven(), positiveInfinity,
		FloatingPointFromUint64(8, 24, 0xbf800000),
	)
	if !FloatingPointIsInfinite(negative) || !FloatingPointIsNegative(negative) {
		t.Fatal("positive infinity times negative finite must be negative infinity")
	}
}

func TestFloatingPointDivBinary32(t *testing.T) {
	modes := []FloatingPointRoundingMode{
		RoundNearestTiesToEven(),
		RoundNearestTiesToAway(),
		RoundTowardPositive(),
		RoundTowardNegative(),
		RoundTowardZero(),
	}
	tests := []struct {
		name        string
		left, right uint64
		want        [5]uint64
	}{
		{"exact", 0x40400000, 0x40000000, [5]uint64{0x3fc00000, 0x3fc00000, 0x3fc00000, 0x3fc00000, 0x3fc00000}},
		{"positive third", 0x3f800000, 0x40400000, [5]uint64{0x3eaaaaab, 0x3eaaaaab, 0x3eaaaaab, 0x3eaaaaaa, 0x3eaaaaaa}},
		{"negative third", 0xbf800000, 0x40400000, [5]uint64{0xbeaaaaab, 0xbeaaaaab, 0xbeaaaaaa, 0xbeaaaaab, 0xbeaaaaaa}},
		{"positive underflow tie", 0x00000001, 0x40000000, [5]uint64{0, 1, 1, 0, 0}},
		{"overflow", 0x7f7fffff, 0x3f000000, [5]uint64{0x7f800000, 0x7f800000, 0x7f800000, 0x7f7fffff, 0x7f7fffff}},
	}
	for _, test := range tests {
		for modeIndex, mode := range modes {
			quotient := FloatingPointDiv(
				mode,
				FloatingPointFromUint64(8, 24, test.left),
				FloatingPointFromUint64(8, 24, test.right),
			)
			got, ok := FloatingPointBits(quotient).Uint64()
			if !ok || got != test.want[modeIndex] {
				t.Fatalf("%s mode %d bits=%#08x,%v, want %#08x,true", test.name, modeIndex, got, ok, test.want[modeIndex])
			}
		}
	}
}

func TestFloatingPointDivSpecialValues(t *testing.T) {
	positiveInfinity := FloatingPointPositiveInfinity(8, 24)
	positiveZero := FloatingPointPositiveZero(8, 24)
	negativeZero := FloatingPointNegativeZero(8, 24)
	one := FloatingPointFromUint64(8, 24, 0x3f800000)
	if !FloatingPointIsNaN(FloatingPointDiv(
		RoundNearestTiesToEven(), positiveInfinity, positiveInfinity,
	)) {
		t.Fatal("infinity divided by infinity must produce NaN")
	}
	if !FloatingPointIsNaN(FloatingPointDiv(
		RoundNearestTiesToEven(), positiveZero, negativeZero,
	)) {
		t.Fatal("zero divided by zero must produce NaN")
	}
	infinite := FloatingPointDiv(
		RoundNearestTiesToEven(), one, negativeZero,
	)
	if !FloatingPointIsInfinite(infinite) || !FloatingPointIsNegative(infinite) {
		t.Fatal("positive finite divided by negative zero must be negative infinity")
	}
	zero := FloatingPointDiv(
		RoundNearestTiesToEven(), one, positiveInfinity,
	)
	if !FloatingPointIsZero(zero) || FloatingPointIsNegative(zero) {
		t.Fatal("positive finite divided by positive infinity must be positive zero")
	}
}

func TestFloatingPointDivBinary128(t *testing.T) {
	one := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x3fff),
		NewBitVectorUint64(112, 0),
	)
	two := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x4000),
		NewBitVectorUint64(112, 0),
	)
	half := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x3ffe),
		NewBitVectorUint64(112, 0),
	)
	quotient := FloatingPointDiv(RoundNearestTiesToEven(), one, two)
	if !EqualBitVectorValue(FloatingPointBits(quotient), FloatingPointBits(half)) {
		t.Fatalf("binary128 fp.div=%v, want %v", FloatingPointBits(quotient), FloatingPointBits(half))
	}
}

func TestFloatingPointFMASingleRounding(t *testing.T) {
	left := FloatingPointFromUint64(8, 24, 0x3f800001)
	right := FloatingPointFromUint64(8, 24, 0x3f7fffff)
	addend := FloatingPointFromUint64(8, 24, 0xbf800000)
	fused := FloatingPointFMA(
		RoundNearestTiesToEven(), left, right, addend,
	)
	got, inline := FloatingPointBits(fused).Uint64()
	if !inline || got != 0x337ffffe {
		t.Fatalf("fused bits=%#x,%v, want 0x337ffffe,true", got, inline)
	}
	separate := FloatingPointAdd(
		RoundNearestTiesToEven(),
		FloatingPointMul(RoundNearestTiesToEven(), left, right),
		addend,
	)
	if !FloatingPointIsZero(separate) {
		t.Fatalf("control multiply-then-add must round to zero, got %v", FloatingPointBits(separate))
	}
}

func TestFloatingPointFMASpecialValues(t *testing.T) {
	infinity := FloatingPointPositiveInfinity(8, 24)
	negativeInfinity := FloatingPointNegativeInfinity(8, 24)
	zero := FloatingPointPositiveZero(8, 24)
	one := FloatingPointFromUint64(8, 24, 0x3f800000)
	if !FloatingPointIsNaN(FloatingPointFMA(
		RoundNearestTiesToEven(), infinity, zero, one,
	)) {
		t.Fatal("infinity times zero in fp.fma must produce NaN")
	}
	if !FloatingPointIsNaN(FloatingPointFMA(
		RoundNearestTiesToEven(), infinity, one, negativeInfinity,
	)) {
		t.Fatal("infinite product plus opposite infinity must produce NaN")
	}
	positive := FloatingPointFMA(
		RoundNearestTiesToEven(), infinity, one, infinity,
	)
	if !FloatingPointIsInfinite(positive) || FloatingPointIsNegative(positive) {
		t.Fatal("positive infinite product plus positive infinity must stay positive infinity")
	}
}

func TestFloatingPointFMAExtremeBinary128Gap(t *testing.T) {
	one := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x3fff),
		NewBitVectorUint64(112, 0),
	)
	minimumSubnormal := FloatingPointFromBits(
		15, 113, NewBitVectorUint64(128, 1),
	)
	nextOne := FloatingPointFromBits(
		15, 113,
		AddBitVectorValue(
			FloatingPointBits(one), NewBitVectorUint64(128, 1),
		),
	)
	for name, fused := range map[string]FloatingPointValue{
		"product dominant": FloatingPointFMA(
			RoundTowardPositive(), one, one, minimumSubnormal,
		),
		"addend dominant": FloatingPointFMA(
			RoundTowardPositive(), minimumSubnormal, minimumSubnormal, one,
		),
	} {
		if !EqualBitVectorValue(
			FloatingPointBits(fused), FloatingPointBits(nextOne),
		) {
			t.Fatalf("%s RTP=%v, want next(1)=%v", name, FloatingPointBits(fused), FloatingPointBits(nextOne))
		}
	}
}

func TestFloatingPointSqrtBinary32(t *testing.T) {
	modes := []FloatingPointRoundingMode{
		RoundNearestTiesToEven(),
		RoundNearestTiesToAway(),
		RoundTowardPositive(),
		RoundTowardNegative(),
		RoundTowardZero(),
	}
	want := [5]uint64{
		0x3fb504f3, 0x3fb504f3, 0x3fb504f4, 0x3fb504f3, 0x3fb504f3,
	}
	for index, mode := range modes {
		root := FloatingPointSqrt(
			mode, FloatingPointFromUint64(8, 24, 0x40000000),
		)
		got, inline := FloatingPointBits(root).Uint64()
		if !inline || got != want[index] {
			t.Fatalf("sqrt(2) mode %d=%#x,%v, want %#x,true", index, got, inline, want[index])
		}
	}
	exact := FloatingPointSqrt(
		RoundNearestTiesToEven(),
		FloatingPointFromUint64(8, 24, 0x40800000),
	)
	got, _ := FloatingPointBits(exact).Uint64()
	if got != 0x40000000 {
		t.Fatalf("sqrt(4)=%#x, want 0x40000000", got)
	}
}

func TestFloatingPointSqrtSpecialValues(t *testing.T) {
	negativeZero := FloatingPointNegativeZero(8, 24)
	if root := FloatingPointSqrt(
		RoundNearestTiesToEven(), negativeZero,
	); !EqualBitVectorValue(FloatingPointBits(root), FloatingPointBits(negativeZero)) {
		t.Fatal("sqrt(-zero) must preserve negative zero")
	}
	if !FloatingPointIsNaN(FloatingPointSqrt(
		RoundNearestTiesToEven(),
		FloatingPointFromUint64(8, 24, 0xbf800000),
	)) {
		t.Fatal("sqrt(negative finite) must produce NaN")
	}
	infinity := FloatingPointPositiveInfinity(8, 24)
	if root := FloatingPointSqrt(
		RoundNearestTiesToEven(), infinity,
	); !FloatingPointIsInfinite(root) || FloatingPointIsNegative(root) {
		t.Fatal("sqrt(+infinity) must be +infinity")
	}
}

func TestFloatingPointSqrtBinary128(t *testing.T) {
	four := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x4001),
		NewBitVectorUint64(112, 0),
	)
	two := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x4000),
		NewBitVectorUint64(112, 0),
	)
	root := FloatingPointSqrt(RoundNearestTiesToEven(), four)
	if !EqualBitVectorValue(FloatingPointBits(root), FloatingPointBits(two)) {
		t.Fatalf("binary128 sqrt(4)=%v, want %v", FloatingPointBits(root), FloatingPointBits(two))
	}
}

func TestFloatingPointRemBinary32(t *testing.T) {
	tests := []struct {
		name        string
		left, right uint64
		want        uint64
	}{
		{"three by two tie", 0x40400000, 0x40000000, 0xbf800000},
		{"five by two tie", 0x40a00000, 0x40000000, 0x3f800000},
		{"negative five by two", 0xc0a00000, 0x40000000, 0xbf800000},
		{"smaller dividend", 0x3f000000, 0x40000000, 0x3f000000},
		{"exact multiple", 0x40800000, 0x40000000, 0x00000000},
	}
	for _, test := range tests {
		remainder := FloatingPointRem(
			FloatingPointFromUint64(8, 24, test.left),
			FloatingPointFromUint64(8, 24, test.right),
		)
		got, inline := FloatingPointBits(remainder).Uint64()
		if !inline || got != test.want {
			t.Fatalf("%s=%#x,%v, want %#x,true", test.name, got, inline, test.want)
		}
	}
}

func TestFloatingPointRemSpecialValues(t *testing.T) {
	one := FloatingPointFromUint64(8, 24, 0x3f800000)
	zero := FloatingPointPositiveZero(8, 24)
	infinity := FloatingPointPositiveInfinity(8, 24)
	if !FloatingPointIsNaN(FloatingPointRem(infinity, one)) {
		t.Fatal("infinite dividend remainder must be NaN")
	}
	if !FloatingPointIsNaN(FloatingPointRem(one, zero)) {
		t.Fatal("remainder by zero must be NaN")
	}
	if remainder := FloatingPointRem(one, infinity); !EqualBitVectorValue(
		FloatingPointBits(remainder), FloatingPointBits(one),
	) {
		t.Fatal("finite remainder by infinity must preserve the dividend")
	}
	negativeZero := FloatingPointNegativeZero(8, 24)
	if remainder := FloatingPointRem(negativeZero, one); !EqualBitVectorValue(
		FloatingPointBits(remainder), FloatingPointBits(negativeZero),
	) {
		t.Fatal("zero remainder must preserve the dividend sign")
	}
}

func TestFloatingPointRemBinary128HugeGap(t *testing.T) {
	one := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 0),
		NewBitVectorUint64(15, 0x3fff),
		NewBitVectorUint64(112, 0),
	)
	minimumSubnormal := FloatingPointFromBits(
		15, 113, NewBitVectorUint64(128, 1),
	)
	remainder := FloatingPointRem(one, minimumSubnormal)
	if !FloatingPointIsZero(remainder) || FloatingPointIsNegative(remainder) {
		t.Fatalf("1 rem minimum binary128 subnormal=%v, want +zero", FloatingPointBits(remainder))
	}
}

func TestFloatingPointToBitVectorModesAndBounds(t *testing.T) {
	tests := []struct {
		name      string
		raw       uint64
		mode      FloatingPointRoundingMode
		width     int
		signed    bool
		want      uint64
		wantValid bool
	}{
		{"unsigned tie even", 0x3fc00000, RoundNearestTiesToEven(), 8, false, 2, true},
		{"unsigned tie away", 0x3fc00000, RoundNearestTiesToAway(), 8, false, 2, true},
		{"unsigned toward zero", 0x3fe66666, RoundTowardZero(), 8, false, 1, true},
		{"unsigned toward positive", 0x3f8ccccd, RoundTowardPositive(), 8, false, 2, true},
		{"unsigned negative invalid", 0xbf800000, RoundNearestTiesToEven(), 8, false, 0, false},
		{"signed negative", 0xbfc00000, RoundNearestTiesToEven(), 8, true, 0xfe, true},
		{"signed minimum", 0xc3000000, RoundNearestTiesToEven(), 8, true, 0x80, true},
		{"signed positive overflow", 0x43000000, RoundNearestTiesToEven(), 8, true, 0, false},
		{"unsigned maximum", 0x437f0000, RoundNearestTiesToEven(), 8, false, 0xff, true},
		{"unsigned overflow", 0x43800000, RoundNearestTiesToEven(), 8, false, 0, false},
		{"nan unspecified", 0x7fc00000, RoundNearestTiesToEven(), 8, false, 0, false},
		{"infinity unspecified", 0x7f800000, RoundNearestTiesToEven(), 8, true, 0, false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			value := FloatingPointFromUint64(8, 24, test.raw)
			var got BitVectorValue
			var valid bool
			if test.signed {
				got, valid = FloatingPointToSignedBitVector(
					test.width, test.mode, value,
				)
			} else {
				got, valid = FloatingPointToUnsignedBitVector(
					test.width, test.mode, value,
				)
			}
			if valid != test.wantValid {
				t.Fatalf("valid = %v, want %v", valid, test.wantValid)
			}
			if raw, ok := got.Uint64(); !ok || raw != test.want {
				t.Fatalf("bits = %#x, want %#x", raw, test.want)
			}
		})
	}
}

func TestFloatingPointToSignedBitVectorBinary128(t *testing.T) {
	value := FloatingPointFromComponents(
		15, 113,
		NewBitVectorUint64(1, 1),
		NewBitVectorUint64(15, 16390),
		NewBitVectorUint64(112, 0),
	)
	got, valid := FloatingPointToSignedBitVector(
		130, RoundNearestTiesToEven(), value,
	)
	if !valid {
		t.Fatal("expected valid binary128 conversion")
	}
	want := IntegerToBitVectorValue(130, NewIntegerValue(-128))
	if !EqualBitVectorValue(got, want) {
		t.Fatalf("got %v, want %v", BitVectorToIntegerValue(got, true), BitVectorToIntegerValue(want, true))
	}
}

func TestFloatingPointToBitVectorSynthesizesUnconstrainedSource(t *testing.T) {
	for _, test := range []struct {
		name   string
		signed bool
		target uint64
		want   uint64
	}{
		{"unsigned", false, 3, 0x40400000},
		{"signed-negative", true, 0xfd, 0xc0400000},
		{"zero", false, 0, 0},
	} {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointToBitVectorRelation(
				8, 24, 8, 1, RoundNearestTiesToEven(),
				test.signed, NewBitVectorUint64(8, test.target),
			)
			result, ok := Check(AssertFloatingPointToBitVectorRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatal("expected synthesized fp.to_bv source")
			}
			source, found := FloatingPointSymbolModelBits(result.Value, 1)
			raw, inline := source.Uint64()
			if !found || !inline || raw != test.want {
				t.Fatalf("source=%#x, found=%v, want %#x", raw, found, test.want)
			}
		})
	}
}

func TestFloatingPointToBitVectorLeavesNonimageUnknown(t *testing.T) {
	relation := NewFloatingPointToBitVectorRelation(
		8, 24, 32, 1, RoundNearestTiesToEven(), false,
		NewBitVectorUint64(32, 0x01000001),
	)
	if _, ok := Check(AssertFloatingPointToBitVectorRelation(
		1, New(), relation,
	)).(Unknown); !ok {
		t.Fatal("nonimage fp.to_bv result must remain unknown")
	}
}

func TestFloatingPointToBitVectorSynthesizesWideBinary128Source(t *testing.T) {
	target := IntegerToBitVectorValue(130, NewIntegerValue(-128))
	relation := NewFloatingPointToBitVectorRelation(
		15, 113, 130, 1, RoundNearestTiesToEven(), true, target,
	)
	result, ok := Check(AssertFloatingPointToBitVectorRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized wide binary128 fp.to_bv source")
	}
	source, found := FloatingPointSymbolModelBits(result.Value, 1)
	if !found || source.Width() != 128 {
		t.Fatal("binary128 fp.to_bv source missing from model")
	}
}

func TestFloatingPointFromBitVectorModes(t *testing.T) {
	tests := []struct {
		name   string
		value  uint64
		width  int
		signed bool
		mode   FloatingPointRoundingMode
		want   uint64
	}{
		{"unsigned exact", 3, 8, false, RoundNearestTiesToEven(), 0x40400000},
		{"signed negative", 0xfd, 8, true, RoundNearestTiesToEven(), 0xc0400000},
		{"unsigned high bit", 0xfd, 8, false, RoundNearestTiesToEven(), 0x437d0000},
		{"tie even", 0x01000001, 32, false, RoundNearestTiesToEven(), 0x4b800000},
		{"tie away", 0x01000001, 32, false, RoundNearestTiesToAway(), 0x4b800001},
		{"toward positive", 0x01000001, 32, false, RoundTowardPositive(), 0x4b800001},
		{"toward zero", 0x01000001, 32, false, RoundTowardZero(), 0x4b800000},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			value := NewBitVectorUint64(test.width, test.value)
			var got FloatingPointValue
			if test.signed {
				got = FloatingPointFromSignedBitVector(
					8, 24, test.mode, value,
				)
			} else {
				got = FloatingPointFromUnsignedBitVector(
					8, 24, test.mode, value,
				)
			}
			raw, inline := FloatingPointBits(got).Uint64()
			if !inline || raw != test.want {
				t.Fatalf("bits = %#x, want %#x", raw, test.want)
			}
		})
	}
}

func TestFloatingPointFromBitVectorSynthesizesUnconstrainedSource(t *testing.T) {
	for _, test := range []struct {
		name   string
		signed bool
		target uint64
		want   uint64
	}{
		{"signed-negative", true, 0xc0400000, 0xfd},
		{"unsigned", false, 0x437d0000, 0xfd},
		{"zero", false, 0, 0},
	} {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointFromBitVectorRelation(
				8, 24, 8, 1, RoundNearestTiesToEven(),
				test.signed, NewBitVectorUint64(32, test.target),
			)
			result, ok := Check(AssertFloatingPointFromBitVectorRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatal("expected synthesized BV-to-FP source")
			}
			source, found := FloatingPointSymbolModelBits(result.Value, 1)
			raw, inline := source.Uint64()
			if !found || !inline || raw != test.want {
				t.Fatalf("source=%#x, found=%v, want %#x", raw, found, test.want)
			}
		})
	}
}

func TestFloatingPointFromBitVectorRejectsImpossibleResults(t *testing.T) {
	for _, target := range []uint64{
		0x3fc00000, // noninteger
		0x80000000, // negative zero
		0x7fc00000, // NaN
		0xff800000, // unsigned negative infinity
	} {
		relation := NewFloatingPointFromBitVectorRelation(
			8, 24, 8, 1, RoundNearestTiesToEven(), false,
			NewBitVectorUint64(32, target),
		)
		if _, ok := Check(AssertFloatingPointFromBitVectorRelation(
			1, New(), relation,
		)).(Unsatisfiable); !ok {
			t.Fatalf("expected result %#x to be impossible", target)
		}
	}
}

func TestFloatingPointFromBitVectorSynthesizesWideBinary128Source(t *testing.T) {
	target := FloatingPointBits(FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(), NewRational(-128, 1),
	))
	relation := NewFloatingPointFromBitVectorRelation(
		15, 113, 130, 1, RoundNearestTiesToEven(), true, target,
	)
	result, ok := Check(AssertFloatingPointFromBitVectorRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized wide BV-to-binary128 source")
	}
	source, found := FloatingPointSymbolModelBits(result.Value, 1)
	if !found || source.Width() != 130 ||
		CompareIntegerValue(
			BitVectorToIntegerValue(source, true), NewIntegerValue(-128),
		) != 0 {
		t.Fatal("unexpected wide BV-to-binary128 source")
	}
}

func TestFloatingPointFromBitVectorSynthesizesInfinityOverflow(t *testing.T) {
	target := FloatingPointBits(FloatingPointPositiveInfinity(5, 11))
	relation := NewFloatingPointFromBitVectorRelation(
		5, 11, 130, 1, RoundNearestTiesToEven(), false, target,
	)
	if _, ok := Check(AssertFloatingPointFromBitVectorRelation(
		1, New(), relation,
	)).(Satisfiable); !ok {
		t.Fatal("expected maximum unsigned BV to synthesize +infinity")
	}
}

func TestFloatingPointConvertFormat(t *testing.T) {
	t.Run("special values preserve class and zero sign", func(t *testing.T) {
		if got := FloatingPointConvertFormat(
			5, 11, RoundNearestTiesToEven(),
			FloatingPointFromUint64(8, 24, 0x80000000),
		); floatingPointTestBits64(t, got) != 0x8000 {
			t.Fatalf("negative zero = %#x", floatingPointTestBits64(t, got))
		}
		if got := FloatingPointConvertFormat(
			5, 11, RoundNearestTiesToEven(),
			FloatingPointFromUint64(8, 24, 0xff800000),
		); floatingPointTestBits64(t, got) != 0xfc00 {
			t.Fatalf("negative infinity = %#x", floatingPointTestBits64(t, got))
		}
		if got := FloatingPointConvertFormat(
			5, 11, RoundNearestTiesToEven(),
			FloatingPointFromUint64(8, 24, 0x7fc12345),
		); !FloatingPointIsNaN(got) {
			t.Fatalf("NaN converted to %#x", floatingPointTestBits64(t, got))
		}
	})

	// 1 + 2^-11 is exactly halfway between binary16 1.0 and its successor.
	source := FloatingPointFromUint64(8, 24, 0x3f801000)
	tests := []struct {
		mode FloatingPointRoundingMode
		want uint64
	}{
		{RoundNearestTiesToEven(), 0x3c00},
		{RoundNearestTiesToAway(), 0x3c01},
		{RoundTowardPositive(), 0x3c01},
		{RoundTowardNegative(), 0x3c00},
		{RoundTowardZero(), 0x3c00},
	}
	for _, test := range tests {
		got := FloatingPointConvertFormat(5, 11, test.mode, source)
		if bits := floatingPointTestBits64(t, got); bits != test.want {
			t.Fatalf("mode %#v = %#x, want %#x", test.mode, bits, test.want)
		}
	}

	wide := FloatingPointFromBits(
		15, 113,
		bitVectorValueFromBig(
			128,
			new(big.Int).Lsh(big.NewInt(0x3fff), 112),
		),
	)
	if got := FloatingPointConvertFormat(
		8, 24, RoundNearestTiesToEven(), wide,
	); floatingPointTestBits64(t, got) != 0x3f800000 {
		t.Fatalf("binary128 one converted to %#x", floatingPointTestBits64(t, got))
	}
}

func TestFloatingPointFromRational(t *testing.T) {
	// 1 + 2^-24 is exactly halfway between binary32 1.0 and its successor.
	value := NewRational(16777217, 16777216)
	tests := []struct {
		mode FloatingPointRoundingMode
		want uint64
	}{
		{RoundNearestTiesToEven(), 0x3f800000},
		{RoundNearestTiesToAway(), 0x3f800001},
		{RoundTowardPositive(), 0x3f800001},
		{RoundTowardNegative(), 0x3f800000},
		{RoundTowardZero(), 0x3f800000},
	}
	for _, test := range tests {
		got := FloatingPointFromRational(8, 24, test.mode, value)
		if bits := floatingPointTestBits64(t, got); bits != test.want {
			t.Fatalf("mode %#v = %#x, want %#x", test.mode, bits, test.want)
		}
	}
	negative := FloatingPointFromRational(
		8, 24, RoundTowardZero(), NewRational(-3, 2),
	)
	if bits := floatingPointTestBits64(t, negative); bits != 0xbfc00000 {
		t.Fatalf("-3/2 = %#x", bits)
	}
	wide := FloatingPointFromRational(
		15, 113, RoundNearestTiesToEven(),
		MustParseRational(
			"340282366920938463463374607431768211457/340282366920938463463374607431768211456",
		),
	)
	if !FloatingPointIsNormal(wide) {
		t.Fatal("arbitrary-precision rational did not produce a normal value")
	}
}

func TestFloatingPointFromRealRelation(t *testing.T) {
	real := RealSymbol{ID: 1}
	assignment := Equal{
		Left: real, Right: Real{Value: NewRational(16777217, 16777216)},
	}
	relation := NewFloatingPointFromRealRelation(
		8, 24, 1, RoundNearestTiesToEven(),
		NewBitVectorUint64(32, 0x3f800000),
	)
	result := Check(AssertFloatingPointFromRealRelation(
		2, Assert(1, New(), assignment), relation,
	))
	if _, ok := result.(Satisfiable); !ok {
		t.Fatalf("result=%T", result)
	}
	relation.Value = NewBitVectorUint64(32, 0x3f800001)
	result = Check(AssertFloatingPointFromRealRelation(
		2, Assert(1, New(), assignment), relation,
	))
	if _, ok := result.(Unsatisfiable); !ok {
		t.Fatalf("contradictory result=%T", result)
	}
}

func TestFloatingPointToRational(t *testing.T) {
	tests := []struct {
		bits  uint64
		value Rational
	}{
		{0x00000000, Rational{}},
		{0x80000000, Rational{}},
		{0x3fc00000, NewRational(3, 2)},
		{0xc0600000, NewRational(-7, 2)},
		{0x00000001, MustParseRational("1/713623846352979940529142984724747568191373312")},
	}
	for _, test := range tests {
		value, valid := FloatingPointToRational(
			FloatingPointFromUint64(8, 24, test.bits),
		)
		if !valid || CompareRational(value, test.value) != 0 {
			t.Fatalf("%#x = %s,%v, want %s", test.bits, value, valid, test.value)
		}
	}
	for _, bits := range []uint64{0x7f800000, 0x7fc12345} {
		if _, valid := FloatingPointToRational(
			FloatingPointFromUint64(8, 24, bits),
		); valid {
			t.Fatalf("%#x unexpectedly has a defined Real value", bits)
		}
	}
}

func TestFloatingPointToRealRelation(t *testing.T) {
	symbol := BitVecConst(32, 1, "value")
	assignment := BitVectorRelation{
		Width: 32, SymbolID: 1,
		Value: NewBitVectorUint64(32, 0x3fc00000),
	}
	relation := NewFloatingPointToRealRelation(
		8, 24, 1, NewRational(3, 2),
	)
	result := Check(AssertFloatingPointToRealRelation(
		2, Assert(1, New(), assignment), relation,
	))
	if _, ok := result.(Satisfiable); !ok {
		t.Fatalf("result=%T symbol=%#v", result, symbol)
	}
	relation.Value = NewRational(7, 4)
	result = Check(AssertFloatingPointToRealRelation(
		2, Assert(1, New(), assignment), relation,
	))
	if _, ok := result.(Unsatisfiable); !ok {
		t.Fatalf("contradictory result=%T", result)
	}
}

func TestFloatingPointToRealSynthesizesUnconstrainedSource(t *testing.T) {
	relation := NewFloatingPointToRealRelation(
		8, 24, 1, NewRational(3, 2),
	)
	result, ok := Check(AssertFloatingPointToRealRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected exact fp.to_real preimage")
	}
	bits, found := FloatingPointSymbolModelBits(result.Value, 1)
	raw, inline := bits.Uint64()
	if !found || !inline || raw != 0x3fc00000 {
		t.Fatalf("source bits=%#x, found=%v", raw, found)
	}

	unrepresentable := NewFloatingPointToRealRelation(
		8, 24, 1, NewRational(1, 10),
	)
	if _, ok := Check(AssertFloatingPointToRealRelation(
		1, New(), unrepresentable,
	)).(Unknown); !ok {
		t.Fatal("unrepresentable finite preimage must remain unknown")
	}
}

func TestFloatingPointToRealSynthesizesBinary128Source(t *testing.T) {
	relation := NewFloatingPointToRealRelation(
		15, 113, 1, NewRational(-7, 4),
	)
	result, ok := Check(AssertFloatingPointToRealRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected exact binary128 fp.to_real preimage")
	}
	bits, found := FloatingPointSymbolModelBits(result.Value, 1)
	if !found || bits.Width() != 128 {
		t.Fatal("binary128 source missing from model")
	}
	converted, valid := FloatingPointToRational(
		FloatingPointFromBits(15, 113, bits),
	)
	if !valid || CompareRational(converted, NewRational(-7, 4)) != 0 {
		t.Fatalf("binary128 source converts to %v", converted)
	}
}

func TestFloatingPointToRealSynthesizesAffinePreimage(t *testing.T) {
	relation := NewFloatingPointToRealInlineRelation(
		[4]FloatingPointToRealTerm{{
			ExponentBits: 8, SignificandBits: 24, SymbolID: 1,
			Coefficient: NewRational(2, 1),
		}},
		1, NewRational(1, 2), 0,
	)
	result, ok := Check(AssertFloatingPointToRealRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected exact affine fp.to_real preimage")
	}
	bits, found := FloatingPointSymbolModelBits(result.Value, 1)
	raw, inline := bits.Uint64()
	if !found || !inline || raw != 0xbe800000 {
		t.Fatalf("affine source bits=%#x, found=%v", raw, found)
	}
}

func TestFloatingPointFormatConversionSynthesizesUnconstrainedSource(t *testing.T) {
	for _, test := range []struct {
		name                         string
		sourceExponent, sourceSignif int
		targetExponent, targetSignif int
		target                       BitVectorValue
	}{
		{
			"binary32-to-binary16", 8, 24, 5, 11,
			NewBitVectorUint64(16, 0x3c00),
		},
		{
			"binary16-to-binary32", 5, 11, 8, 24,
			NewBitVectorUint64(32, 0x3fc00000),
		},
		{
			"signed-zero", 5, 11, 8, 24,
			NewBitVectorUint64(32, 0x80000000),
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			relation := NewFloatingPointFormatConversionRelation(
				test.sourceExponent, test.sourceSignif,
				test.targetExponent, test.targetSignif,
				1, RoundNearestTiesToEven(), test.target,
			)
			result, ok := Check(AssertFloatingPointFormatConversionRelation(
				1, New(), relation,
			)).(Satisfiable)
			if !ok {
				t.Fatal("expected synthesized format-conversion source")
			}
			source, found := FloatingPointSymbolModelBits(result.Value, 1)
			if !found {
				t.Fatal("format-conversion source missing from model")
			}
			converted := FloatingPointConvertFormat(
				test.targetExponent, test.targetSignif,
				RoundNearestTiesToEven(),
				FloatingPointFromBits(
					test.sourceExponent, test.sourceSignif, source,
				),
			)
			if !EqualBitVectorValue(FloatingPointBits(converted), test.target) {
				t.Fatalf(
					"converted model=%v, want %v",
					FloatingPointBits(converted), test.target,
				)
			}
		})
	}
}

func TestFloatingPointFormatConversionLeavesNonimageUnknown(t *testing.T) {
	relation := NewFloatingPointFormatConversionRelation(
		5, 11, 8, 24, 1, RoundNearestTiesToEven(),
		NewBitVectorUint64(32, 0x3f801000),
	)
	if _, ok := Check(AssertFloatingPointFormatConversionRelation(
		1, New(), relation,
	)).(Unknown); !ok {
		t.Fatal("nonimage format-conversion target must remain unknown")
	}
}

func TestFloatingPointFormatConversionSynthesizesBinary128Source(t *testing.T) {
	target := FloatingPointBits(FloatingPointFromRational(
		8, 24, RoundNearestTiesToEven(), NewRational(-7, 4),
	))
	relation := NewFloatingPointFormatConversionRelation(
		15, 113, 8, 24, 1, RoundNearestTiesToEven(), target,
	)
	result, ok := Check(AssertFloatingPointFormatConversionRelation(
		1, New(), relation,
	)).(Satisfiable)
	if !ok {
		t.Fatal("expected synthesized binary128 format-conversion source")
	}
	source, found := FloatingPointSymbolModelBits(result.Value, 1)
	if !found || source.Width() != 128 {
		t.Fatal("binary128 format-conversion source missing from model")
	}
}

func TestFloatingPointToRealAffineRelation(t *testing.T) {
	solver := Assert(1, New(), BitVectorRelation{
		Width: 32, SymbolID: 1,
		Value: NewBitVectorUint64(32, 0x3fc00000),
	})
	solver = Assert(2, solver, BitVectorRelation{
		Width: 32, SymbolID: 2,
		Value: NewBitVectorUint64(32, 0x40600000),
	})
	terms := []FloatingPointToRealTerm{
		{
			ExponentBits: 8, SignificandBits: 24, SymbolID: 1,
			Coefficient: NewRational(2, 1),
		},
		{
			ExponentBits: 8, SignificandBits: 24, SymbolID: 2,
			Coefficient: NewRational(-1, 1),
		},
	}
	equality := NewFloatingPointToRealAffineRelation(
		terms, NewRational(1, 2), 0,
	)
	if result := Check(AssertFloatingPointToRealRelation(
		3, solver, equality,
	)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("affine equality result=%T", result)
	}
	strict := NewFloatingPointToRealAffineRelation(
		terms, Rational{}, 2,
	)
	if result := Check(AssertFloatingPointToRealRelation(
		3, solver, strict,
	)); func() bool { _, ok := result.(Satisfiable); return ok }() == false {
		t.Fatalf("affine strict-order result=%T", result)
	}
	strict.Negated = true
	if result := Check(AssertFloatingPointToRealRelation(
		3, solver, strict,
	)); func() bool { _, ok := result.(Unsatisfiable); return ok }() == false {
		t.Fatalf("negated affine strict-order result=%T", result)
	}
}

func TestFloatingPointToRealMixedLinearRealRelation(t *testing.T) {
	solver := Assert(1, New(), BitVectorRelation{
		Width: 32, SymbolID: 1,
		Value: NewBitVectorUint64(32, 0x3fc00000),
	})
	relation := NewMixedFloatingPointToRealInlineRelation(
		[4]FloatingPointToRealTerm{{
			ExponentBits: 8, SignificandBits: 24, SymbolID: 1,
			Coefficient: NewRational(1, 1),
		}},
		1,
		[4]FloatingPointToRealRealTerm{{
			SymbolID: 7, Coefficient: NewRational(-1, 1),
		}},
		1, Rational{}, 0,
	)
	result := Check(AssertFloatingPointToRealRelation(2, solver, relation))
	sat, ok := result.(Satisfiable)
	if !ok {
		t.Fatalf("mixed result=%T", result)
	}
	value, found := RealValue(sat.Value, RealSymbol{ID: 7})
	if !found || CompareRational(value, NewRational(3, 2)) != 0 {
		t.Fatalf("mixed Real model=%s,%v", value, found)
	}

	contradiction := LinearRealConstraint{
		Count: 1, Symbols: [4]int{7},
		Coefficients: [4]Rational{NewRational(-1, 1)},
		Constant:     NewRational(2, 1),
	}
	result = Check(Assert(
		3, AssertFloatingPointToRealRelation(2, solver, relation),
		contradiction,
	))
	if _, ok := result.(Unsatisfiable); !ok {
		t.Fatalf("mixed contradiction result=%T", result)
	}
}

func TestFloatingPointFromSignedBitVectorArbitraryWidth(t *testing.T) {
	value := IntegerToBitVectorValue(
		130,
		integerValueFromBig(new(big.Int).Neg(
			new(big.Int).Lsh(big.NewInt(1), 120),
		)),
	)
	got := FloatingPointFromSignedBitVector(
		15, 113, RoundNearestTiesToEven(), value,
	)
	if !FloatingPointIsNegative(got) || FloatingPointIsInfinite(got) {
		t.Fatalf("unexpected binary128 conversion: %#v", FloatingPointBits(got))
	}
	finite := decodeFloatingPointFinite(got)
	if !finite.negative ||
		finite.scale.Sign() < 0 ||
		new(big.Int).Lsh(finite.magnitude, uint(finite.scale.Int64())).Cmp(
			new(big.Int).Lsh(big.NewInt(1), 120),
		) != 0 {
		t.Fatal("binary128 conversion did not preserve exact -2^120")
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
