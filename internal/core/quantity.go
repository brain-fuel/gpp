// Package core is goplus's dependent type theory (v0.7.0): first-order
// terms over nat and enum-tag data, normalization by evaluation,
// definitional equality, a linear-arithmetic decider, structural
// termination checking, and the QTT quantity semiring. The core is
// deliberately independent of the lowering pipeline: it consumes
// elaborated terms and answers judgments; go/types only ever sees the
// erased output.
package core

import "fmt"

// QKind enumerates the quantity semiring's elements.
type QKind int

const (
	Q0     QKind = iota // erased: exists only at check time
	Q1                  // linear: consumed exactly once
	QOmega              // unrestricted
	QVar                // a multiplicity variable [m mult]
)

// Quantity is a QTT multiplicity: 0, 1, ω, or a variable.
type Quantity struct {
	K   QKind
	Var string // for QVar
}

func (q Quantity) String() string {
	switch q.K {
	case Q0:
		return "0"
	case Q1:
		return "1"
	case QOmega:
		return "ω"
	default:
		return q.Var
	}
}

// Add is semiring addition (usage in two positions of one path).
// 0+q=q, 1+1=ω, ω+q=ω; variables only combine with 0.
func Add(a, b Quantity) Quantity {
	switch {
	case a.K == Q0:
		return b
	case b.K == Q0:
		return a
	case a.K == QVar || b.K == QVar:
		return Quantity{K: QOmega} // conservative: m+m and m+1 exceed any single m
	default:
		return Quantity{K: QOmega}
	}
}

// Mul is semiring multiplication (usage under a binder of quantity a).
// 0·q=0, 1·q=q, ω·q = ω unless q=0, m·1=m.
func Mul(a, b Quantity) Quantity {
	switch {
	case a.K == Q0 || b.K == Q0:
		return Quantity{K: Q0}
	case a.K == Q1:
		return b
	case b.K == Q1:
		return a
	case a.K == QVar && b.K == QVar:
		return Quantity{K: QOmega} // v1: no multiplicity products
	default:
		return Quantity{K: QOmega}
	}
}

// LeqUsage reports whether observed usage u is admissible at declared
// quantity d: 0 admits only 0; 1 admits exactly 1; ω admits anything; a
// variable admits 0 or exactly one occurrence of itself.
func LeqUsage(u, d Quantity) bool {
	switch d.K {
	case QOmega:
		return true
	case Q0:
		return u.K == Q0
	case Q1:
		return u.K == Q1
	default:
		return u.K == Q0 || (u.K == QVar && u.Var == d.Var)
	}
}

// ErrQuantity builds a uniform quantity-violation message.
func ErrQuantity(name string, u, d Quantity) error {
	return fmt.Errorf("parameter %s has quantity %s but is used at %s", name, d, u)
}
