// Package canonical defines law-bearing normalization: reducing values to a
// deterministic representative without changing their semantic equivalence.
//
//goplus:laws out=lawtest
package canonical

import "reflect"

// Canonical is a normalizer together with the equivalence relation whose
// classes it represents. Normalize must be idempotent, and two values are
// equivalent exactly when their canonical representatives are structurally
// equal.
type Canonical[T any] class {
	Normalize(value T) T
	Equivalent(a, b T) bool

	law Idempotent(value T) {
		return reflect.DeepEqual(Normalize(Normalize(value)), Normalize(value))
	}
	law Sound(a, b T) {
		if !reflect.DeepEqual(Normalize(a), Normalize(b)) {
			return true
		}
		return Equivalent(a, b)
	}
	law Complete(a, b T) {
		if !Equivalent(a, b) {
			return true
		}
		return reflect.DeepEqual(Normalize(a), Normalize(b))
	}
}
