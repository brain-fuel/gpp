package algebra

// IntAdd is the additive group of integers.
instance IntAdd Group[int] {
	Combine(a, b int) int { return a + b }
	Empty() int { return 0 }
	Invert(a int) int { return -a }
}

// IntMul is the multiplicative monoid of integers.
instance IntMul Monoid[int] {
	Combine(a, b int) int { return a * b }
	Empty() int { return 1 }
}

// StringConcat is the free monoid over strings.
instance StringConcat Monoid[string] {
	Combine(a, b string) string { return a + b }
	Empty() string { return "" }
}

// BoolAnd is conjunction with identity true.
instance BoolAnd Monoid[bool] {
	Combine(a, b bool) bool { return a && b }
	Empty() bool { return true }
}

// BoolOr is disjunction with identity false.
instance BoolOr Monoid[bool] {
	Combine(a, b bool) bool { return a || b }
	Empty() bool { return false }
}

// SliceConcat is the free monoid over slices of any element type.
//
//goplus:laws [int] [string]
instance SliceConcat[T any] Monoid[[]T] {
	Combine(a, b []T) []T { return append(append([]T{}, a...), b...) }
	Empty() []T { return nil }
}

// MinInt is the meet semigroup of integers.
instance MinInt Semigroup[int] {
	Combine(a, b int) int {
		if a < b {
			return a
		}
		return b
	}
}

// MaxInt is the join semigroup of integers.
instance MaxInt Semigroup[int] {
	Combine(a, b int) int {
		if a > b {
			return a
		}
		return b
	}
}
