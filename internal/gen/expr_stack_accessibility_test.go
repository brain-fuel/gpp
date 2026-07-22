package gen

import (
	"path/filepath"
	"strings"
	"testing"
)

func exprConsumerModule(t *testing.T, source string) string {
	t.Helper()
	dir := t.TempDir()
	expr, err := filepath.Abs("../../../expr")
	if err != nil {
		t.Fatal(err)
	}
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/exprproof\n\ngo 1.25.0\n\nrequire goforge.dev/expr v0.0.0\nreplace goforge.dev/expr => "+expr+"\n")
	writeRefinementTestFile(t, dir, "main.gp", source)
	return dir
}

func TestGoPlusConsumesExprStackEffectsAcrossPackage(t *testing.T) {
	dir := exprConsumerModule(t, `package main
import "goforge.dev/expr/typed"
func main() {
	empty := typed.EmptyStack()
	one := typed.PushInteger(0, empty, 20)
	two := typed.PushInteger(1, one, 22)
	add := typed.IntegerAdd(typed.ZeroDepth())
	_ = typed.ExecuteIntegerInstruction(0, add, two)
	_ = typed.TransportStack(2, 1+1, refl, two)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if !res.Ok() {
		t.Fatalf("generation diagnostics: %+v", res.Diags)
	}
}

func TestExprInstructionStackEffectRejectsWrongInstruction(t *testing.T) {
	dir := exprConsumerModule(t, `package main
import "goforge.dev/expr/typed"
func main() {
	empty := typed.EmptyStack()
	one := typed.PushInteger(0, empty, 1)
	two := typed.PushInteger(1, one, 2)
	push := typed.Push(typed.ZeroDepth(), typed.IntValue(3))
	_ = typed.ExecuteIntegerInstruction(0, push, two)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("growth instruction unexpectedly accepted as binary instruction")
	}
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "index") || strings.Contains(diagnostic.Msg, "cannot unify") {
			return
		}
	}
	t.Fatalf("diagnostics do not explain instruction stack effect: %+v", res.Diags)
}

func TestExprStackEqualityWitnessRejectsUnequalDepths(t *testing.T) {
	dir := exprConsumerModule(t, `package main
import "goforge.dev/expr/typed"
func main() {
	empty := typed.EmptyStack()
	one := typed.PushInteger(0, empty, 1)
	_ = typed.TransportStack(1, 2, refl, one)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("unequal stack depths unexpectedly transported by refl")
	}
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "cannot prove") {
			return
		}
	}
	t.Fatalf("diagnostics do not explain equality failure: %+v", res.Diags)
}

func TestExprStackUnderflowRejectedAcrossPackage(t *testing.T) {
	dir := exprConsumerModule(t, `package main
import "goforge.dev/expr/typed"
func main() {
	empty := typed.EmptyStack()
	_ = typed.AddIntegers(0, empty)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("empty stack unexpectedly accepted by n+2 instruction")
	}
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "index") || strings.Contains(diagnostic.Msg, "cannot unify") {
			return
		}
	}
	t.Fatalf("diagnostics do not explain stack-effect mismatch: %+v", res.Diags)
}
