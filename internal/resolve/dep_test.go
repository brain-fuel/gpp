package resolve

import "testing"

func TestConstructorExistentialNatEquality(t *testing.T) {
	variables := map[string]bool{"n": true}
	for _, test := range []struct {
		want, got string
		ok        bool
		supported bool
	}{
		{"2", "n+1+1", true, true},
		{"1", "n+1+1", false, true},
		{"5", "2*n+1", true, true},
		{"4", "2*n+1", false, true},
		{"m+2", "n+2", false, false},
	} {
		got, supported := existsConstructorIndexEquality(test.want, test.got, variables)
		if supported != test.supported || got != test.ok {
			t.Errorf("exists %s = %s: got (%v, %v), want (%v, %v)", test.want, test.got, got, supported, test.ok, test.supported)
		}
	}
}

func TestSubstituteRecursiveIndexIsSimultaneous(t *testing.T) {
	got, err := substTypeTextLite("Vec[T, n+1]", map[string]string{"T": "int", "n": "n+1"})
	if err != nil {
		t.Fatal(err)
	}
	if got != "Vec[int, n+1+1]" {
		t.Fatalf("substitution = %q", got)
	}
}
