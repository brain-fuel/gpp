package vec

import "testing"

func fromSlice(xs []int) Vec[int] {
	v := Vec[int](Nil[int]{})
	for i := len(xs) - 1; i >= 0; i-- {
		v = Cons[int]{Head: xs[i], Tail: v}
	}
	return v
}

func toSlice(v Vec[int]) []int {
	var out []int
	for {
		c, ok := any(v).(Cons[int])
		if !ok {
			return out
		}
		out = append(out, c.Head)
		v = c.Tail
	}
}

func TestFirstRest(t *testing.T) {
	v := fromSlice([]int{1, 2, 3})
	if First(v) != 1 {
		t.Fatalf("First = %d", First(v))
	}
	if got := toSlice(Rest(v)); len(got) != 2 || got[0] != 2 || got[1] != 3 {
		t.Fatalf("Rest = %v", got)
	}
}

func TestConcatLength(t *testing.T) {
	for n := 0; n < 5; n++ {
		for m := 0; m < 5; m++ {
			a, b := toVecN(n), toVecN(m)
			if got := Length(Concat(a, b)); got != n+m {
				t.Fatalf("Length(Concat(%d, %d)) = %d", n, m, got)
			}
		}
	}
}

func toVecN(n int) Vec[int] {
	xs := make([]int, n)
	for i := range xs {
		xs[i] = i
	}
	return fromSlice(xs)
}

func TestReplicateLengthAgree(t *testing.T) {
	for n := 0; n < 6; n++ {
		if got := Length(Replicate(n, "x")); got != n {
			t.Fatalf("Length(Replicate(%d)) = %d", n, got)
		}
	}
}

func TestMapPreservesLength(t *testing.T) {
	v := fromSlice([]int{1, 2, 3})
	w := Map(func(x int) int { return x * 10 }, v)
	if got := toSlice(w); len(got) != 3 || got[0] != 10 {
		t.Fatalf("Map = %v", got)
	}
}

func TestGuardFiresFromPlainGo(t *testing.T) {
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("First(Nil) did not panic")
		}
	}()
	First[int](Nil[int]{})
}
