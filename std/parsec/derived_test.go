package parsec

import (
	"strconv"
	"testing"
	"unicode"
)

func number() Parser[int] {
	return Label(Lexeme(Map(Many1(RuneWhen(unicode.IsDigit, "digit")), func(rs []rune) int {
		n, _ := strconv.Atoi(string(rs))
		return n
	})), "number")
}

func exprParser() Parser[int] {
	var expr Parser[int]
	factor := Or(number(), Between(Symbol("("), Defer(&expr), Symbol(")")))
	mulOp := Or(
		Map(Symbol("*"), func(string) func(int, int) int { return func(a, b int) int { return a * b } }),
		Map(Symbol("/"), func(string) func(int, int) int { return func(a, b int) int { return a / b } }),
	)
	addOp := Or(
		Map(Symbol("+"), func(string) func(int, int) int { return func(a, b int) int { return a + b } }),
		Map(Symbol("-"), func(string) func(int, int) int { return func(a, b int) int { return a - b } }),
	)
	term := Chainl1(factor, mulOp)
	expr = Chainl1(term, addOp)
	return Then(Spaces(), Before(expr, EOF()))
}

func TestExpression(t *testing.T) {
	rows := map[string]int{
		"1+2*3":        7,
		"(1+2)*3":      9,
		" 10 - 4 - 3 ": 3,
		"2*(3+4)/2":    7,
		"((((5))))":    5,
	}
	p := exprParser()
	for src, want := range rows {
		got, err := RunString(p, src)
		if err != nil {
			t.Fatalf("%q: %v", src, err)
		}
		if got != want {
			t.Fatalf("%q = %d, want %d", src, got, want)
		}
	}
	if _, err := RunString(p, "1+*2"); err == nil {
		t.Fatal("malformed input parsed")
	}
}

func TestSepByAndOpt(t *testing.T) {
	list := Between(Symbol("["), SepBy(number(), Symbol(",")), Symbol("]"))
	got, err := RunString(list, "[1, 2, 3]")
	if err != nil || len(got) != 3 || got[2] != 3 {
		t.Fatalf("SepBy: %v %v", got, err)
	}
	empty, err := RunString(list, "[]")
	if err != nil || len(empty) != 0 {
		t.Fatalf("SepBy empty: %v %v", empty, err)
	}
	if v, err := RunString(Opt(number(), -1), "zz"); err != nil || v != -1 {
		t.Fatalf("Opt: %v %v", v, err)
	}
}

func TestManyRejectsEmptyAccepting(t *testing.T) {
	if _, err := RunString(Many(Spaces()), "x"); err == nil {
		t.Fatal("Many(Spaces()) did not fail")
	}
}
