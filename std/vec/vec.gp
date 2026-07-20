// Package vec is a length-indexed sequence: Vec[T, n] carries its
// length in its type, so First and Rest exist only for non-empty
// vectors — the checker proves it, erasure drops it, and the generated
// Go stays a plain cons-list any Go program can use (guarded at the
// exported boundary).
package vec

type Vec[T any, n nat] enum {
	Nil() Vec[T, 0]
	Cons(Head T, Tail Vec[T, n]) Vec[T, n+1]
}

// First returns the head of a non-empty vector.
func First[T any](0 n nat, v Vec[T, n+1]) T {
	match v {
	case Cons(h, t):
		_ = t
		return h
	}
}

// Rest returns everything after the head of a non-empty vector.
func Rest[T any](0 n nat, v Vec[T, n+1]) Vec[T, n] {
	match v {
	case Cons(h, t):
		_ = h
		return t
	}
}

// Length walks the spine; the result equals the index by construction.
func Length[T any](0 n nat, v Vec[T, n]) int {
	total := 0
	match v {
	case Nil():
	case Cons(h, t):
		_ = h
		total = Length(t) + 1
	}
	return total
}

// Replicate builds the vector of n copies of x.
func Replicate[T any](n nat, x T) Vec[T, n] {
	if n == 0 {
		return Nil[T]()
	}
	return Cons(x, Replicate(n-1, x))
}

// Concat appends b to a; the indices add.
func Concat[T any](0 n nat, 0 m nat, a Vec[T, n], b Vec[T, m]) Vec[T, n+m] {
	match a {
	case Nil():
		return b
	case Cons(h, t):
		return Cons(h, Concat(t, b))
	}
}

// Map transforms every element, preserving the length.
func Map[T any, U any](0 n nat, f func(T) U, v Vec[T, n]) Vec[U, n] {
	match v {
	case Nil():
		return Nil[U]()
	case Cons(h, t):
		return Cons(f(h), Map(f, t))
	}
}
