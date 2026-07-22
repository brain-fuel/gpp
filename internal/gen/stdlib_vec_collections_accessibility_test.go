package gen

import (
	"bytes"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func vecConsumerModule(t *testing.T, source string) string {
	t.Helper()
	dir := t.TempDir()
	std, err := filepath.Abs("../../std")
	if err != nil {
		t.Fatal(err)
	}
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/veccollections\n\ngo 1.24.0\n\nrequire goforge.dev/goplus/std v0.0.0\nreplace goforge.dev/goplus/std => "+std+"\n")
	writeRefinementTestFile(t, dir, "main.gp", source)
	return dir
}

func TestGoPlusConsumesEqualLengthZipAndBoundedAt(t *testing.T) {
	dir := vecConsumerModule(t, `package main

import (
	"fmt"
	"goforge.dev/goplus/std/vec"
)

func main() {
	left := vec.Cons(1, vec.Cons(2, vec.Nil[int]()))
	right := vec.Cons("a", vec.Cons("b", vec.Nil[string]()))
	zipped := vec.Zip(2, left, right)
	index := vec.Succ(vec.Zero())
	fmt.Println(vec.At(2, index, left), vec.Length(2, zipped))
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
		t.Fatalf("Go+ vec consumer: %v\n%s", err, stderr.Bytes())
	}
	if got := stdout.String(); got != "2 2\n" {
		t.Fatalf("output = %q", got)
	}
}

func TestEqualLengthZipRejectsDifferentShapes(t *testing.T) {
	dir := vecConsumerModule(t, `package main
import "goforge.dev/goplus/std/vec"
func main() {
	left := vec.Cons(1, vec.Cons(2, vec.Nil[int]()))
	right := vec.Cons("a", vec.Nil[string]())
	_ = vec.Zip(2, left, right)
}
`)
	assertDependentCollectionReject(t, dir, "different vector lengths unexpectedly zipped")
}

func TestBoundedAtRejectsOutOfRangeEvidence(t *testing.T) {
	dir := vecConsumerModule(t, `package main
import "goforge.dev/goplus/std/vec"
func main() {
	values := vec.Cons(1, vec.Nil[int]())
	index := vec.Succ(vec.Zero())
	_ = vec.At(1, index, values)
}
`)
	assertDependentCollectionReject(t, dir, "out-of-range Fin evidence unexpectedly type checked")
}

func assertDependentCollectionReject(t *testing.T, dir, message string) {
	t.Helper()
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal(message)
	}
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "index") || strings.Contains(diagnostic.Msg, "cannot unify") {
			return
		}
	}
	t.Fatalf("diagnostics do not explain dependent mismatch: %+v", res.Diags)
}
