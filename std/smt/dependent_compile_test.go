package smt

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestSortedTermsAcrossPackageBoundary(t *testing.T) {
	tool := filepath.Join(t.TempDir(), "goplus")
	build := exec.Command("go", "build", "-o", tool, "./cmd/goplus")
	build.Dir = filepath.Join("..", "..")
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build Go+ tool: %v\n%s", err, out)
	}
	stdDir, err := filepath.Abs("..")
	if err != nil {
		t.Fatal(err)
	}

	compile := func(t *testing.T, source string) (string, error) {
		t.Helper()
		dir := t.TempDir()
		module := "module fixture\n\ngo 1.26.0\n\nrequire goforge.dev/goplus/std v0.0.0\nreplace goforge.dev/goplus/std => " + stdDir + "\n"
		if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte(module), 0o600); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, "main.gp"), []byte(source), 0o600); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(tool, "gen", ".")
		cmd.Dir = dir
		out, err := cmd.CombinedOutput()
		return string(out), err
	}

	positive := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { _ = smt.Equal(smt.Bool(true), smt.Bool(false)) }\n"
	if out, err := compile(t, positive); err != nil {
		t.Fatalf("same-sort equality failed: %v\n%s", err, out)
	}

	negative := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { _ = smt.Equal(smt.Bool(true), smt.Integer(1)) }\n"
	out, err := compile(t, negative)
	if err == nil {
		t.Fatalf("mixed-sort equality unexpectedly compiled:\n%s", out)
	}
	if !strings.Contains(out, "fields sharing a hidden type parameter must have the same instantiation") {
		t.Fatalf("unexpected diagnostic: %s", out)
	}

	eufPositive := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { a := smt.UninterpretedConstant(1, 1, \"a\"); f := smt.DeclareUnaryFunction(1, 2, 1, \"f\"); _ = smt.ApplyUnary(f, a) }\n"
	if out, err := compile(t, eufPositive); err != nil {
		t.Fatalf("well-sorted unary application failed: %v\n%s", err, out)
	}

	eufNegative := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { a := smt.UninterpretedConstant(3, 1, \"a\"); f := smt.DeclareUnaryFunction(1, 2, 1, \"f\"); _ = smt.ApplyUnary(f, a) }\n"
	out, err = compile(t, eufNegative)
	if err == nil {
		t.Fatalf("ill-sorted unary application unexpectedly compiled:\n%s", out)
	}
	if !strings.Contains(out, "dependent index mismatch") {
		t.Fatalf("unexpected unary application diagnostic: %s", out)
	}

	conversionPositive := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc accept8(value smt.Term[smt.BitVecSort[8]]) {}\nfunc main() { accept8(smt.IntToBitVec(8, smt.Integer(257))); _ = smt.BitVecToNat(smt.BitVecVal(8, 255)); _ = smt.BitVecToInt(smt.BitVecVal(8, 255)) }\n"
	if out, err := compile(t, conversionPositive); err != nil {
		t.Fatalf("well-indexed conversions failed: %v\n%s", err, out)
	}

	conversionNegative := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { var value smt.Term[smt.BitVecSort[16]] = smt.IntToBitVec(8, smt.Integer(257)); _ = value }\n"
	out, err = compile(t, conversionNegative)
	if err == nil {
		t.Fatalf("mismatched conversion width unexpectedly compiled:\n%s", out)
	}
	if !strings.Contains(out, "dependent index mismatch") {
		t.Fatalf("unexpected conversion diagnostic: %s", out)
	}

	arrayPositive := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { a := smt.ArrayConst[smt.IntSort, smt.BoolSort](1, \"a\"); _ = smt.Store(a, smt.Integer(1), smt.Bool(true)); _ = smt.Select(a, smt.Integer(1)) }\n"
	if out, err := compile(t, arrayPositive); err != nil {
		t.Fatalf("well-sorted array operations failed: %v\n%s", err, out)
	}

	arrayNegative := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { a := smt.ArrayConst[smt.IntSort, smt.BoolSort](1, \"a\"); _ = smt.Store(a, smt.Bool(true), smt.Bool(false)) }\n"
	out, err = compile(t, arrayNegative)
	if err == nil {
		t.Fatalf("ill-sorted array store unexpectedly compiled:\n%s", out)
	}

	bitVectorArrayPositive := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { a := smt.ArrayConst[smt.BitVecSort[4], smt.BitVecSort[8]](1, \"a\"); _ = smt.Store(a, smt.BitVecVal(4, 3), smt.BitVecVal(8, 0xa5)); var value smt.Term[smt.BitVecSort[8]] = smt.Select(a, smt.BitVecVal(4, 3)); _ = value }\n"
	if out, err := compile(t, bitVectorArrayPositive); err != nil {
		t.Fatalf("well-indexed bit-vector array failed: %v\n%s", err, out)
	}

	datatypePositive := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { x := smt.DatatypeConst(1, 3, 1, \"x\"); red := smt.DatatypeConstructor(1, 3, 0, \"red\"); _ = smt.Equal(x, red); _ = smt.IsDatatypeConstructor(1, 3, 0, x) }\n"
	if out, err := compile(t, datatypePositive); err != nil {
		t.Fatalf("well-indexed finite datatype failed: %v\n%s", err, out)
	}

	datatypeNegative := "package main\nimport \"goforge.dev/goplus/std/smt\"\nfunc main() { left := smt.DatatypeConst(1, 3, 1, \"left\"); right := smt.DatatypeConst(2, 3, 2, \"right\"); _ = smt.Equal(left, right) }\n"
	out, err = compile(t, datatypeNegative)
	if err == nil {
		t.Fatalf("cross-datatype equality unexpectedly compiled:\n%s", out)
	}
	if !strings.Contains(out, "dependent index mismatch") && !strings.Contains(out, "same instantiation") {
		t.Fatalf("unexpected datatype diagnostic: %s", out)
	}

}
