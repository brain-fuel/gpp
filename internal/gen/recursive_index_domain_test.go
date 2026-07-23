package gen

import (
	"strings"
	"testing"
)

func TestRecursiveIndexDomainTypesHeterogeneousList(t *testing.T) {
	dir := t.TempDir()
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/recursiveindex\n\ngo 1.26.0\n")
	writeRefinementTestFile(t, dir, "main.gp", `package main

type FieldSort enum { IntegerField(); SelfField() }
type Fields enum { NoFields(); More(Head FieldSort, Tail Fields) }

type Arguments[fields Fields] enum {
	NoArguments() Arguments[NoFields]
	argumentsValue(Values []any) Arguments[fields]
}

func IntegerArgument(0 tail Fields, value int, rest Arguments[tail]) Arguments[More(IntegerField, tail)] { return argumentsValue([]any{value, rest}) }
func SelfArgument(0 tail Fields, value string, rest Arguments[tail]) Arguments[More(SelfField, tail)] { return argumentsValue([]any{value, rest}) }
func Need(values Arguments[More(IntegerField, More(SelfField, NoFields))]) {}
func main() { Need(IntegerArgument(42, SelfArgument("leaf", NoArguments()))) }
`)
	result, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if !result.Ok() {
		t.Fatalf("valid recursive index domain rejected: %+v", result.Diags)
	}
}

func TestRecursiveIndexDomainRejectsWrongHeterogeneousOrder(t *testing.T) {
	dir := t.TempDir()
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/recursiveindexbad\n\ngo 1.26.0\n")
	writeRefinementTestFile(t, dir, "main.gp", `package main

type FieldSort enum { IntegerField(); SelfField() }
type Fields enum { NoFields(); More(Head FieldSort, Tail Fields) }

type Arguments[fields Fields] enum {
	NoArguments() Arguments[NoFields]
	argumentsValue(Values []any) Arguments[fields]
}

func IntegerArgument(0 tail Fields, value int, rest Arguments[tail]) Arguments[More(IntegerField, tail)] { return argumentsValue([]any{value, rest}) }
func SelfArgument(0 tail Fields, value string, rest Arguments[tail]) Arguments[More(SelfField, tail)] { return argumentsValue([]any{value, rest}) }
func Need(values Arguments[More(IntegerField, More(SelfField, NoFields))]) {}
func main() { Need(SelfArgument("leaf", IntegerArgument(42, NoArguments()))) }
`)
	result, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if result.Ok() {
		t.Fatal("wrong heterogeneous field order unexpectedly accepted")
	}
	for _, diagnostic := range result.Diags {
		if strings.Contains(diagnostic.Msg, "dependent index mismatch") {
			return
		}
	}
	t.Fatalf("diagnostics do not explain recursive index mismatch: %+v", result.Diags)
}
