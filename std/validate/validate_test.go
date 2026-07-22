package validate

import (
	"testing"

	"goforge.dev/goplus/std/config"
)

const (
	requiredPredicate = 1
	minimumPredicate  = 2
)

func requiredStringRule() Rule[string] {
	return Atom[string](requiredPredicate, "required", "", func(value string) bool { return value != "" })
}

func minimumLengthRule(minimum int) Rule[string] {
	return Atom[string](minimumPredicate, "min", "3", func(value string) bool { return len(value) >= minimum })
}

type account struct {
	Name  string
	Token string
}

func accountRule() Rule[account] {
	name := At(Field("Name", func(value account) string { return value.Name }), requiredStringRule())
	token := At(Field("Token", func(value account) string { return value.Token }), minimumLengthRule(3))
	return And(name, token)
}

func TestAtomicValidationAndWitness(t *testing.T) {
	rule := requiredStringRule()
	accepted := Validate(rule, "value")
	if failures := FailuresOf(accepted); failures != nil {
		t.Fatalf("accepted value has failures: %v", failures)
	}
	value := accepted.(Accepted[string]).Value
	if Value(value) != "value" || !Revalidate(rule, value) {
		t.Fatal("validated witness did not retain value/rule")
	}
	other := Atom[string](99, "other", "", func(string) bool { return true })
	if Revalidate(other, value) {
		t.Fatal("plain Go mixed different predicate witnesses")
	}

	rejected := Validate(rule, "")
	failures := FailuresOf(rejected)
	if len(failures) != 1 || failures[0].Code != "required" || failures.Error() != "required" {
		t.Fatalf("failures = %#v (%q)", failures, failures.Error())
	}
}

func TestConjunctionAndTypedPaths(t *testing.T) {
	rule := accountRule()
	failures := FailuresOf(Validate(rule, account{}))
	if len(failures) != 2 {
		t.Fatalf("got %d failures: %v", len(failures), failures)
	}
	if failures[0].Path != "Name" || failures[0].Code != "required" || failures[1].Path != "Token" || failures[1].Param != "3" {
		t.Fatalf("unexpected stable failures: %#v", failures)
	}
	if failures.Error() != "Name: required; Token: min=3" {
		t.Fatalf("Error = %q", failures.Error())
	}
	if !PredicateEqual(PredicateOfRule(rule), Both{Left: Named{ID: 1}, Right: Named{ID: 2}}) {
		t.Fatal("conjunction predicate witness differs")
	}
}

func TestConjunctionLaws(t *testing.T) {
	left, right := requiredStringRule(), minimumLengthRule(3)
	for _, value := range []string{"", "x", "valid"} {
		got := Check(And(left, right), value)
		want := append(Check(left, value), Check(right, value)...)
		if len(got) != len(want) {
			t.Fatalf("Check(And) failures for %q = %v, want %v", value, got, want)
		}
		for i := range got {
			if got[i] != want[i] {
				t.Fatalf("Check(And) failure %d for %q = %v, want %v", i, value, got[i], want[i])
			}
		}
	}
	for _, predicate := range []Predicate{Named{ID: 1}, Both{Left: Named{ID: 1}, Right: Named{ID: 2}}} {
		if !PredicateEqual(predicate, predicate) {
			t.Fatalf("PredicateEqual is not reflexive for %#v", predicate)
		}
	}
	if PredicateEqual(Both{Left: Named{ID: 1}, Right: Named{ID: 2}}, Both{Left: Named{ID: 2}, Right: Named{ID: 1}}) {
		t.Fatal("ordered conjunctions unexpectedly compare equal")
	}
}

func TestMapRevalidates(t *testing.T) {
	rule := requiredStringRule()
	value := Validate(rule, "ok").(Accepted[string]).Value
	if failures := FailuresOf(Map(value, func(string) string { return "" })); len(failures) != 1 {
		t.Fatalf("Map failures = %#v", failures)
	}
	if got := Value(Map(value, func(v string) string { return v + "!" }).(Accepted[string]).Value); got != "ok!" {
		t.Fatalf("Map value = %q", got)
	}
}

func TestConfigIntegration(t *testing.T) {
	var validator config.Validator[account] = AsConfigValidator(accountRule())
	if err := validator.Validate(account{Name: "alice", Token: "abc"}); err != nil {
		t.Fatal(err)
	}
	if err := validator.Validate(account{}); err == nil {
		t.Fatal("invalid config passed")
	}
}

func TestConstructionGuards(t *testing.T) {
	for _, construct := range []func(){
		func() { _ = Atom[string](-1, "negative", "", func(string) bool { return true }) },
		func() { _ = Atom[string](1, "", "", func(string) bool { return true }) },
		func() { _ = Atom[string](1, "code", "", nil) },
		func() { _ = Field[string, string]("", func(v string) string { return v }) },
		func() { _ = Field[string, string]("Value", nil) },
	} {
		func() {
			defer func() {
				if recover() == nil {
					t.Error("construction did not panic")
				}
			}()
			construct()
		}()
	}
}

func BenchmarkCoreFieldSuccess(b *testing.B) {
	rule := requiredStringRule()
	b.ReportAllocs()
	for b.Loop() {
		_ = Check(rule, "value")
	}
}

func BenchmarkCoreFieldFailure(b *testing.B) {
	rule := requiredStringRule()
	b.ReportAllocs()
	for b.Loop() {
		_ = Check(rule, "")
	}
}

func BenchmarkCoreStructSuccess(b *testing.B) {
	rule := accountRule()
	value := account{Name: "alice", Token: "abc"}
	b.ReportAllocs()
	for b.Loop() {
		_ = Check(rule, value)
	}
}

func BenchmarkCoreStructFailure(b *testing.B) {
	rule := accountRule()
	value := account{}
	b.ReportAllocs()
	for b.Loop() {
		_ = Check(rule, value)
	}
}
