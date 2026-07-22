package gen

import (
	"bytes"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func decimalConsumerModule(t *testing.T, source string) string {
	t.Helper()
	dir := t.TempDir()
	std, err := filepath.Abs("../../std")
	if err != nil {
		t.Fatal(err)
	}
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/decimalaccess\n\ngo 1.24.0\n\nrequire goforge.dev/goplus/std v0.0.0\nreplace goforge.dev/goplus/std => "+std+"\n")
	writeRefinementTestFile(t, dir, "main.gp", source)
	return dir
}

// This separate-module test proves that generated markers reconstruct both
// the Precision refinement and the erased Fixed[p] index for consumers.
func TestGoPlusConsumesIndexedDecimal(t *testing.T) {
	dir := decimalConsumerModule(t, `package main

import (
	"fmt"
	"goforge.dev/goplus/std/decimal"
)

func addAtScale(0 p nat, a decimal.Fixed[p], b decimal.Fixed[p]) decimal.Fixed[p] {
	return decimal.AddFixed(a, b)
}

func main() {
	a := decimal.Quantize(2, decimal.RequireFromString("1.234"), decimal.HalfEven{})
	c := decimal.Quantize(2, decimal.RequireFromString("0.77"), decimal.HalfEven{})
	_ = addAtScale(2, a, c)
	b := decimal.Quantize(3, decimal.RequireFromString("2.345"), decimal.HalfEven{})
	product := decimal.MulFixed(2, 3, a, b)
	rescaled := decimal.RescaleFixed(5, 2, product, decimal.HalfEven{})
	fmt.Println(decimal.FixedDecimal(2, rescaled))
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
		t.Fatalf("Go+ decimal consumer: %v\n%s", err, stderr.Bytes())
	}
	if got := stdout.String(); got != "2.88\n" {
		t.Fatalf("output = %q", got)
	}
}

func TestIndexedDecimalRejectsMixedScales(t *testing.T) {
	dir := decimalConsumerModule(t, `package main

import "goforge.dev/goplus/std/decimal"

func main() {
	a := decimal.Quantize(2, decimal.One, decimal.HalfEven{})
	b := decimal.Quantize(3, decimal.One, decimal.HalfEven{})
	_ = decimal.AddFixed(2, a, b)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("mixed Fixed[2]/Fixed[3] scales unexpectedly type checked")
	}
	found := false
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "index") || strings.Contains(diagnostic.Msg, "cannot unify") {
			found = true
		}
	}
	if !found {
		t.Fatalf("diagnostics do not explain index mismatch: %+v", res.Diags)
	}
}

func TestIndexedDecimalRejectsReassignedIndex(t *testing.T) {
	dir := decimalConsumerModule(t, `package main

import "goforge.dev/goplus/std/decimal"

func main() {
	a := decimal.Quantize(2, decimal.One, decimal.HalfEven{})
	b := decimal.Quantize(2, decimal.One, decimal.HalfEven{})
	a = decimal.Quantize(3, decimal.One, decimal.HalfEven{})
	_ = decimal.AddFixed(2, a, b)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("reassigned indexed value unexpectedly type checked")
	}
	found := false
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "reassigned value a") {
			found = true
		}
	}
	if !found {
		t.Fatalf("diagnostics do not explain unstable index: %+v", res.Diags)
	}
}
