package option

import (
	"strconv"
	"testing"
)

func TestPresence(t *testing.T) {
	// Of enters from comma-ok pairs.
	m := map[string]int{"a": 1}
	v, ok := m["a"]
	if got := Of(v, ok); !IsSome(got) {
		t.Fatalf("Of present: %v", got)
	}
	v, ok = m["b"]
	if got := Of(v, ok); !IsNone(got) {
		t.Fatalf("Of absent: %v", got)
	}

	// Map lifts; None passes through.
	if got := Map(Some[int]{Value: 7}, strconv.Itoa); got != (Some[string]{Value: "7"}) {
		t.Fatalf("Map some: %v", got)
	}
	if got := Map(None[int]{}, strconv.Itoa); got != (None[string]{}) {
		t.Fatalf("Map none: %v", got)
	}

	// Bind chains; None bypasses.
	half := func(n int) Option[int] {
		if n%2 != 0 {
			return None[int]{}
		}
		return Some[int]{Value: n / 2}
	}
	if got := Bind(Some[int]{Value: 8}, half); got != (Some[int]{Value: 4}) {
		t.Fatalf("Bind even: %v", got)
	}
	if got := Bind(Some[int]{Value: 7}, half); got != (None[int]{}) {
		t.Fatalf("Bind odd: %v", got)
	}
	if got := Bind(None[int]{}, half); got != (None[int]{}) {
		t.Fatalf("Bind none: %v", got)
	}

	// UnwrapOr and OrElse.
	if got := UnwrapOr(Some[int]{Value: 3}, 9); got != 3 {
		t.Fatalf("UnwrapOr some: %v", got)
	}
	if got := UnwrapOr(None[int]{}, 9); got != 9 {
		t.Fatalf("UnwrapOr none: %v", got)
	}
	if got := OrElse[int](None[int]{}, Some[int]{Value: 5}); got != (Some[int]{Value: 5}) {
		t.Fatalf("OrElse none: %v", got)
	}
	if got := OrElse[int](Some[int]{Value: 2}, Some[int]{Value: 5}); got != (Some[int]{Value: 2}) {
		t.Fatalf("OrElse some: %v", got)
	}

	// Get leaves in comma-ok shape.
	if v, ok := Get(Some[int]{Value: 6}); !ok || v != 6 {
		t.Fatalf("Get some: %v %v", v, ok)
	}
	if v, ok := Get(None[int]{}); ok || v != 0 {
		t.Fatalf("Get none: %v %v", v, ok)
	}

	// Fold folds.
	show := OptionCases[int, string]{
		Some: strconv.Itoa,
		None: func() string { return "-" },
	}
	if got := Fold[int, string](Some[int]{Value: 4}, show); got != "4" {
		t.Fatalf("Fold some: %v", got)
	}
	if got := Fold[int, string](None[int]{}, show); got != "-" {
		t.Fatalf("Fold none: %v", got)
	}
}
