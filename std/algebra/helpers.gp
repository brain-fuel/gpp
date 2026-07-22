package algebra

import "goforge.dev/goplus/std/nonempty"

// Accumulate folds a slice through a monoid, seeded with its identity.
func Accumulate[T Monoid](xs []T) T {
	acc := Empty()
	for _, x := range xs {
		acc = Combine(acc, x)
	}
	return acc
}

// FoldMap maps each element into a monoid and accumulates the results.
func FoldMap[A any, M Monoid](xs []A, f func(A) M) M {
	acc := Empty()
	for _, x := range xs {
		acc = Combine(acc, f(x))
	}
	return acc
}

// ReduceNonEmpty folds a semigroup without inventing an identity and without
// an empty-input panic. This is one independent consumer of std/nonempty; the
// GoForge collection compatibility module is the other.
func ReduceNonEmpty[T Semigroup](xs nonempty.NonEmpty[T]) T {
	return nonempty.Reduce1(xs, func(a, b T) T { return Combine(a, b) })
}
