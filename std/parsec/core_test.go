package parsec

import (
	"strings"
	"testing"
	"unicode"
)

func TestRuneAndStr(t *testing.T) {
	if v, err := RunString(Rune('a'), "abc"); err != nil || v != 'a' {
		t.Fatalf("Rune: %v %q", err, v)
	}
	if v, err := RunString(Str("hello"), "hello!"); err != nil || v != "hello" {
		t.Fatalf("Str: %v %q", err, v)
	}
	if _, err := RunString(Str("hello"), "help"); err == nil {
		t.Fatal("Str partial matched")
	}
}

func TestOrCommitsOnConsumption(t *testing.T) {
	p := Or(Str("ab"), Str("ac"))
	if _, err := RunString(p, "ab"); err != nil {
		t.Fatal(err)
	}
	// "ac": Str("ab") consumes 'a' then fails — committed, no fallback.
	if _, err := RunString(p, "ac"); err == nil {
		t.Fatal("Or fell back after consumption")
	}
	// Try restores the lookahead.
	q := Or(Try(Str("ab")), Str("ac"))
	if v, err := RunString(q, "ac"); err != nil || v != "ac" {
		t.Fatalf("Try(Or): %v %q", err, v)
	}
}

func TestBindSequences(t *testing.T) {
	digits := TakeWhile(unicode.IsDigit)
	p := Bind(digits, func(a string) Parser[string] {
		return Bind(Rune(','), func(_ rune) Parser[string] {
			return Map(digits, func(b string) string { return a + "|" + b })
		})
	})
	if v, err := RunString(p, "12,34"); err != nil || v != "12|34" {
		t.Fatalf("Bind: %v %q", err, v)
	}
}

func TestLabelAndPositions(t *testing.T) {
	p := Bind(Str("a\nb"), func(_ string) Parser[rune] {
		return Label(Rune('x'), "the letter x")
	})
	_, err := RunString(p, "a\nbz")
	if err == nil {
		t.Fatal("expected failure")
	}
	msg := err.Error()
	if !strings.Contains(msg, "2:2") || !strings.Contains(msg, "expecting the letter x") || !strings.Contains(msg, "'z'") {
		t.Fatalf("error message %q", msg)
	}
}

func TestEOF(t *testing.T) {
	p := Bind(Str("ok"), func(s string) Parser[string] {
		return Map(EOF(), func(_ struct{}) string { return s })
	})
	if _, err := RunString(p, "ok"); err != nil {
		t.Fatal(err)
	}
	if _, err := RunString(p, "ok!"); err == nil {
		t.Fatal("EOF matched with input left")
	}
}
