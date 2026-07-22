package nonempty

import (
	"reflect"
	"testing"

	"goforge.dev/goplus/std/option"
)

func TestConstructionOwnershipAndTotalOperations(t *testing.T) {
	source := []int{1, 2, 3}
	wrapped := FromSlice(source)
	some, ok := wrapped.(option.Some[NonEmpty[int]])
	if !ok {
		t.Fatalf("FromSlice = %#v", wrapped)
	}
	source[0], source[1] = 99, 99
	value := some.Value
	if Head(value) != 1 || Last(value) != 3 || Len(value) != 3 {
		t.Fatalf("value changed through source alias: %v", Slice(value))
	}
	tail := Tail(value)
	tail[0] = 88
	if got := Slice(value); !reflect.DeepEqual(got, []int{1, 2, 3}) {
		t.Fatalf("Tail aliases value: %v", got)
	}
	if _, ok := FromSlice([]int{}).(option.None[NonEmpty[int]]); !ok {
		t.Fatal("empty input did not produce None")
	}
}

func TestMapReduceAppendLaws(t *testing.T) {
	left, right := Of(1, 2), Of(3, 4)
	joined := Append(left, right)
	if got := Slice(joined); !reflect.DeepEqual(got, []int{1, 2, 3, 4}) {
		t.Fatalf("Append = %v", got)
	}
	if got := Slice(Map(joined, func(value int) int { return value * 2 })); !reflect.DeepEqual(got, []int{2, 4, 6, 8}) {
		t.Fatalf("Map = %v", got)
	}
	if got := Reduce1(joined, func(a, b int) int { return a + b }); got != 10 {
		t.Fatalf("Reduce1 = %d", got)
	}
	if !reflect.DeepEqual(Slice(Append(Append(left, right), Of(5))), Slice(Append(left, Append(right, Of(5))))) {
		t.Fatal("Append is not associative")
	}
}
