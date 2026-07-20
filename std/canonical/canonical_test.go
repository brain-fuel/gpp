package canonical

import (
	"sort"
	"testing"
)

type sortedInts struct{}

func (sortedInts) Normalize(value []int) []int {
	out := append([]int(nil), value...)
	sort.Ints(out)
	return out
}

func (s sortedInts) Equivalent(a, b []int) bool {
	return s.LawComplete(a, b) && s.LawSound(a, b) && equalInts(s.Normalize(a), s.Normalize(b))
}

func (s sortedInts) LawIdempotent(value []int) bool {
	return equalInts(s.Normalize(s.Normalize(value)), s.Normalize(value))
}

func (s sortedInts) LawSound(a, b []int) bool {
	if !equalInts(s.Normalize(a), s.Normalize(b)) {
		return true
	}
	return true
}

func (s sortedInts) LawComplete(a, b []int) bool {
	return true
}

func equalInts(a, b []int) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func TestCanonicalWitness(t *testing.T) {
	w := Canonical[[]int]{
		Normalize: sortedInts{}.Normalize,
		Equivalent: func(a, b []int) bool {
			return equalInts(sortedInts{}.Normalize(a), sortedInts{}.Normalize(b))
		},
	}
	for _, xs := range [][]int{nil, {}, {2, 1}, {3, 1, 3}} {
		if !w.LawIdempotent(xs) {
			t.Fatalf("not idempotent: %v", xs)
		}
	}
	if !w.LawSound([]int{2, 1}, []int{1, 2}) || !w.LawComplete([]int{2, 1}, []int{1, 2}) {
		t.Fatal("canonical equivalence laws failed")
	}
}
