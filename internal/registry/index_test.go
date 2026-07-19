package registry

import "testing"

func TestEraseIndexArgs(t *testing.T) {
	vec := func(name string) (map[int]bool, int, bool) {
		switch name {
		case "Vec":
			return map[int]bool{1: true}, 2, true
		case "Fin":
			return map[int]bool{0: true}, 1, true
		case "Grid":
			return map[int]bool{1: true, 2: true}, 3, true
		}
		return nil, 0, false
	}
	rows := [][2]string{
		{"Vec[T, n]", "Vec[T]"},
		{"Vec[T, n+1]", "Vec[T]"},
		{"Fin[n]", "Fin"},
		{"Grid[T, n, m]", "Grid[T]"},
		{"[]Vec[T, n]", "[]Vec[T]"},
		{"map[string]Vec[int, n*2]", "map[string]Vec[int]"},
		{"func(Vec[T, n]) Fin[n+1]", "func(Vec[T]) Fin"},
		{"Pair[Vec[T, n], Fin[m]]", "Pair[Vec[T], Fin]"},
		{"T", "T"},
		{"Other[T, n]", "Other[T, n]"},
	}
	for _, r := range rows {
		got, err := EraseIndexArgs(r[0], vec)
		if err != nil {
			t.Fatalf("%s: %v", r[0], err)
		}
		if got != r[1] {
			t.Errorf("EraseIndexArgs(%q) = %q, want %q", r[0], got, r[1])
		}
	}
}

func TestSplitBinders(t *testing.T) {
	types, idx := SplitBinders("T any, n nat")
	if len(types) != 1 || types[0] != "T" || len(idx) != 1 || idx[0].Name != "n" || idx[0].Pos != 1 {
		t.Fatalf("SplitBinders: %v %v", types, idx)
	}
}
