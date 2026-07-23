package resolve

import (
	"go/parser"
	"testing"
)

func TestExprTextPreservesCompositeTypeExpressions(t *testing.T) {
	for _, want := range []string{
		"[]int",
		"map[string][]int",
		"pkg.Pair[int, []string]",
		"func(int) (string, error)",
	} {
		expr, err := parser.ParseExpr(want)
		if err != nil {
			t.Fatal(err)
		}
		if got := exprText(expr); got != want {
			t.Fatalf("exprText(%q) = %q", want, got)
		}
	}
}

func TestUnifyTextBindsCompositeSubexpression(t *testing.T) {
	bind := map[string]string{}
	if !unifyText("[]T", "[][]int", map[string]bool{"T": true}, bind) {
		t.Fatal("unification failed")
	}
	if got := bind["T"]; got != "[]int" {
		t.Fatalf("T = %q", got)
	}
}

func TestUnifyDependentInstantiationBindsMultiIndexNestedType(t *testing.T) {
	bind := map[string]string{}
	if !unifyText("Term[X]", "Term[DatatypeSort[1, 3]]", map[string]bool{"X": true}, bind) {
		pat, perr := parser.ParseExpr("Term[X]")
		arg, aerr := parser.ParseExpr("Term[DatatypeSort[1, 3]]")
		t.Fatalf("direct nested multi-index unification failed: %T/%v vs %T/%v", pat, perr, arg, aerr)
	}
	bind = map[string]string{}
	if !unifyDependentInstantiation("Term[X]", "Term[DatatypeSort[1, 3]]", map[string]bool{"X": true}, bind) {
		t.Fatal("nested multi-index unification failed")
	}
	if got := bind["X"]; got != "DatatypeSort[1, 3]" {
		t.Fatalf("X = %q", got)
	}
}

func TestUnifyDependentInstantiationBindsRecursiveDomainIndex(t *testing.T) {
	bind := map[string]string{}
	if !unifyDependentInstantiation("Arguments[tail]", "Arguments[NoFields]", map[string]bool{"tail": true}, bind) {
		t.Fatal("recursive domain index unification failed")
	}
	if got := bind["tail"]; got != "NoFields" {
		t.Fatalf("tail = %q", got)
	}
}
