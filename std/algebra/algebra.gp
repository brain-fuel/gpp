// Package algebra is the Go+ algebraic hierarchy: eight classes from
// Magma to Group, related by embedding, with each structure's laws
// declared exactly where the structure earns them.
//
// An algebraic structure here is what it is in mathematics: a carrier
// set (the instantiating type T) together with one or more operations on
// it, satisfying stated laws. An instance names one concrete structure —
// the carrier, its operations, and (by passing the generated law tests)
// evidence for its laws. Instances are law-tested by default; the
// generated tests live in the nested lawtest module so this package
// keeps zero dependencies.
//
//goplus:laws out=lawtest
package algebra

import "reflect"

// Magma is a pair (T, Combine): a nonempty carrier set T with a closed
// binary operation Combine: T × T → T. Nothing more is promised —
// closure is the type system's job, and no laws apply.
type Magma[T any] class {
	Combine(a, b T) T
}

// UnitalMagma is a triple (T, Combine, Empty): a magma with a two-sided
// identity element Empty(), which combined with any element — on either
// side — yields that element: Combine(Empty(), a) == a and
// Combine(a, Empty()) == a.
type UnitalMagma[T any] class {
	Magma[T]
	Empty() T
	law LeftId(a T) { return reflect.DeepEqual(Combine(Empty(), a), a) }
	law RightId(a T) { return reflect.DeepEqual(Combine(a, Empty()), a) }
}

// Quasigroup is a triple (T, Combine, division): a magma in which
// division is always possible — LeftDiv(a, b) is the solution x of
// Combine(b, x) == a, and RightDiv(a, b) the solution x of
// Combine(x, b) == a (the Latin-square property).
type Quasigroup[T any] class {
	Magma[T]
	LeftDiv(a, b T) T
	RightDiv(a, b T) T
	law LeftDivCancels(a, b T) { return reflect.DeepEqual(Combine(b, LeftDiv(a, b)), a) }
	law RightDivCancels(a, b T) { return reflect.DeepEqual(Combine(RightDiv(a, b), b), a) }
}

// Loop is a quasigroup with a two-sided identity: divisibility and a
// unit, but no promise of associativity.
type Loop[T any] class {
	UnitalMagma[T]
	Quasigroup[T]
}

// Semigroup is a magma whose operation is associative:
// Combine(Combine(a, b), c) == Combine(a, Combine(b, c)). Grouping
// never matters; order still may.
type Semigroup[T any] class {
	Magma[T]
	law Assoc(a, b, c T) { return reflect.DeepEqual(Combine(Combine(a, b), c), Combine(a, Combine(b, c))) }
}

// AssociativeQuasigroup is a quasigroup whose operation associates.
// (Mathematically every associative quasigroup is a group; the class
// exists as the operational meet of Semigroup and Quasigroup, for
// structures presented without an explicit unit or inverse.)
type AssociativeQuasigroup[T any] class {
	Semigroup[T]
	Quasigroup[T]
}

// Monoid is a triple (T, Combine, Empty): an associative unital magma —
// a semigroup with a two-sided identity. The workhorse of folding:
// Accumulate and FoldMap require exactly this much structure.
type Monoid[T any] class {
	Semigroup[T]
	UnitalMagma[T]
}

// Group is a quadruple (T, Combine, Empty, Invert): a monoid in which
// every element has a two-sided inverse — Combine(a, Invert(a)) ==
// Combine(Invert(a), a) == Empty(). Invertibility makes both divisions
// derivable (LeftDiv(a, b) = Combine(Invert(b), a); RightDiv(a, b) =
// Combine(a, Invert(b))), so Group carries their defaults: instances
// provide Combine, Empty, and Invert only.
type Group[T any] class {
	Monoid[T]
	AssociativeQuasigroup[T]
	Invert(a T) T
	LeftDiv(a, b T) T { return Combine(Invert(b), a) }
	RightDiv(a, b T) T { return Combine(a, Invert(b)) }
	law LeftInverse(a T) { return reflect.DeepEqual(Combine(Invert(a), a), Empty()) }
	law RightInverse(a T) { return reflect.DeepEqual(Combine(a, Invert(a)), Empty()) }
}
