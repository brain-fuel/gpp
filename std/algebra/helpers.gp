package algebra

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
