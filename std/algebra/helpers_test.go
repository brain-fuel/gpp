package algebra

import (
	"testing"

	"goforge.dev/goplus/std/nonempty"
)

func TestReduceNonEmptyConsumer(t *testing.T) {
	if got := ReduceNonEmpty(StringConcat.AsSemigroup(), nonempty.Of("go", "+", "forge")); got != "go+forge" {
		t.Fatalf("ReduceNonEmpty = %q", got)
	}
	if got := ReduceNonEmpty(MinInt, nonempty.Of(7, 3, 9)); got != 3 {
		t.Fatalf("ReduceNonEmpty(MinInt) = %d", got)
	}
}
