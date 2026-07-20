// Package kleene is Kleene's strong three-valued logic (K3): the truth
// value of a proposition that may be undetermined — a header not yet seen,
// a stream half not yet observed, a sensor not yet read. Connectives
// short-circuit on their dominant value (And on False, Or on True) and
// absorb Undetermined otherwise, so a partial observation set yields a
// definite answer exactly when one is logically forced.
//
// Authored in Go+ and distributed as generated Go — consumers never need
// the goplus toolchain.
package kleene

import "iter"

// Value is a K3 truth value.
type Value enum {
	// True is definitely true.
	True
	// False is definitely false.
	False
	// Undetermined is not yet known: the evidence seen so far forces
	// neither True nor False.
	Undetermined
}

// FromBool embeds two-valued logic.
func FromBool(b bool) Value {
	if b {
		return True
	}
	return False
}

// Def exits at the comma-ok boundary: (truth, determined). An
// Undetermined value reports ok=false with a false truth.
func Def(v Value) (bool, bool) {
	match v {
	case True:
		return true, true
	case False:
		return false, true
	case Undetermined:
		return false, false
	}
}

// Resolve collapses Undetermined to the caller's default.
func Resolve(v Value, undetermined bool) bool {
	match v {
	case True:
		return true
	case False:
		return false
	case Undetermined:
		return undetermined
	}
}

// Not is K3 negation: Undetermined passes through.
func Not(v Value) Value {
	match v {
	case True:
		return False
	case False:
		return True
	case Undetermined:
		return Undetermined
	}
}

// And is K3 conjunction: False dominates, then Undetermined absorbs.
func And(a Value, b Value) Value {
	match a {
	case False:
		return False
	case Undetermined:
		match b {
		case False:
			return False
		case True:
			return Undetermined
		case Undetermined:
			return Undetermined
		}
	case True:
		return b
	}
}

// Or is K3 disjunction: True dominates, then Undetermined absorbs.
func Or(a Value, b Value) Value {
	match a {
	case True:
		return True
	case Undetermined:
		match b {
		case True:
			return True
		case False:
			return Undetermined
		case Undetermined:
			return Undetermined
		}
	case False:
		return b
	}
}

// All is n-ary And over a sequence, short-circuiting on the first False.
// The empty sequence is True (the conjunctive identity).
func All(vs iter.Seq[Value]) Value {
	var acc Value = True
	for v := range vs {
		match v {
		case False:
			return False
		case Undetermined:
			acc = Undetermined
		case True:
			// no-op: True is the identity.
		}
	}
	return acc
}

// Any is n-ary Or over a sequence, short-circuiting on the first True.
// The empty sequence is False (the disjunctive identity).
func Any(vs iter.Seq[Value]) Value {
	var acc Value = False
	for v := range vs {
		match v {
		case True:
			return True
		case Undetermined:
			acc = Undetermined
		case False:
			// no-op: False is the identity.
		}
	}
	return acc
}
