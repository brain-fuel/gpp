package gen

import (
	"bytes"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func validateConsumerModule(t *testing.T, source string) string {
	t.Helper()
	dir := t.TempDir()
	std, err := filepath.Abs("../../std")
	if err != nil {
		t.Fatal(err)
	}
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/validateaccess\n\ngo 1.24.0\n\nrequire goforge.dev/goplus/std v0.0.0\nreplace goforge.dev/goplus/std => "+std+"\n")
	writeRefinementTestFile(t, dir, "main.gp", source)
	return dir
}

func TestGoPlusConsumesPredicateIndexedValidation(t *testing.T) {
	dir := validateConsumerModule(t, `package main

import (
	"fmt"
	"goforge.dev/goplus/std/validate"
)

func requireBoth(0 p nat, rule validate.Rule[string, p], value string) validate.Outcome[string, p] {
	return validate.Validate(rule, value)
}

func main() {
	required := validate.Atom[string](1, "required", "", func(value string) bool { return value != "" })
	long := validate.Atom[string](2, "min", "3", func(value string) bool { return len(value) >= 3 })
	both := validate.And(validate.PredicateAtomID(1), validate.PredicateAtomID(2), required, long)
	outcome := requireBoth(validate.PredicateBothID(validate.PredicateAtomID(1), validate.PredicateAtomID(2)), both, "valid")
	match outcome {
	case validate.Accepted(value):
		fmt.Println(validate.Value(validate.PredicateBothID(validate.PredicateAtomID(1), validate.PredicateAtomID(2)), value))
	case validate.Rejected(_):
		fmt.Println("rejected")
	}
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if !res.Ok() {
		t.Fatalf("generation diagnostics: %+v", res.Diags)
	}
	cmd := exec.Command("go", "run", "-mod=mod", ".")
	cmd.Dir = dir
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("Go+ validate consumer: %v\n%s", err, stderr.Bytes())
	}
	if got := stdout.String(); got != "valid\n" {
		t.Fatalf("output = %q", got)
	}
}

func TestPredicateIndexedValidationRejectsMixedWitnesses(t *testing.T) {
	dir := validateConsumerModule(t, `package main

import "goforge.dev/goplus/std/validate"

func requireSame(0 p nat, left validate.Rule[string, p], right validate.Rule[string, p]) {}

func main() {
	required := validate.Atom[string](1, "required", "", func(value string) bool { return value != "" })
	other := validate.Atom[string](2, "other", "", func(string) bool { return true })
	requireSame(validate.PredicateAtomID(1), required, other)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("outcome with a different predicate witness unexpectedly type checked")
	}
	found := false
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "dependent index mismatch") {
			found = true
		}
	}
	if !found {
		t.Fatalf("diagnostics do not explain predicate mismatch: %+v", res.Diags)
	}
}

func TestPredicateIndexedValidationRejectsMismatchedOutcome(t *testing.T) {
	dir := validateConsumerModule(t, `package main

import "goforge.dev/goplus/std/validate"

func accept(0 p nat, outcome validate.Outcome[string, p]) {}

func main() {
	required := validate.Atom[string](1, "required", "", func(value string) bool { return value != "" })
	accept(validate.PredicateAtomID(2), validate.Validate(validate.PredicateAtomID(1), required, "ok"))
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("outcome with a different predicate witness unexpectedly type checked")
	}
	found := false
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "dependent index mismatch") {
			found = true
		}
	}
	if !found {
		t.Fatalf("diagnostics do not explain outcome mismatch: %+v", res.Diags)
	}
}
