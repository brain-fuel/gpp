// Property tests for parsec's combinator algebra. These live in a
// nested module so the std module itself stays dependency-free.
package parsectest

import (
	"io"
	"strings"
	"testing"
	"unicode"

	"pgregory.net/rapid"

	"goforge.dev/goplus/std/parsec"
)

// chunkReader yields at most n bytes per read.
type chunkReader struct {
	s string
	i int
	n int
}

func (c *chunkReader) Read(p []byte) (int, error) {
	if c.i >= len(c.s) {
		return 0, io.EOF
	}
	end := c.i + c.n
	if end > len(c.s) {
		end = len(c.s)
	}
	m := copy(p, c.s[c.i:end])
	c.i += m
	return m, nil
}

// genParser draws a small parser over letters/digits along with a
// description of what it accepts (for cross-checking).
func genParser(t *rapid.T) parsec.Parser[string] {
	switch rapid.IntRange(0, 3).Draw(t, "kind") {
	case 0:
		s := rapid.StringMatching(`[ab]{1,3}`).Draw(t, "lit")
		return parsec.Str(s)
	case 1:
		return parsec.TakeWhile(unicode.IsDigit)
	case 2:
		a := rapid.StringMatching(`[ab]{1,2}`).Draw(t, "a")
		b := rapid.StringMatching(`[ab]{1,2}`).Draw(t, "b")
		return parsec.Or(parsec.Try(parsec.Str(a)), parsec.Str(b))
	default:
		s := rapid.StringMatching(`[ab]{1,2}`).Draw(t, "many")
		return parsec.Map(parsec.Many(parsec.Try(parsec.Str(s))), func(vs []string) string {
			return strings.Join(vs, "")
		})
	}
}

func genInput(t *rapid.T) string {
	return rapid.StringMatching(`[ab0-9]{0,8}`).Draw(t, "input")
}

// run captures outcome + final offset for comparison.
func observe(p parsec.Parser[string], in parsec.Input) (string, int, bool) {
	v, off, ok := "", in.Off, false
	parsec.Fold(p(in), parsec.ReplyCases[string, struct{}]{
		ConsumedOk: func(val string, rest parsec.Input) struct{} {
			v, off, ok = val, rest.Off, true
			return struct{}{}
		},
		EmptyOk: func(val string, rest parsec.Input) struct{} {
			v, off, ok = val, rest.Off, true
			return struct{}{}
		},
		ConsumedErr: func(e parsec.ParseError) struct{} { return struct{}{} },
		EmptyErr:    func(e parsec.ParseError) struct{} { return struct{}{} },
	})
	return v, off, ok
}

func TestBindMonadLaws(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		p := genParser(t)
		src := genInput(t)
		f := func(s string) parsec.Parser[string] {
			return parsec.Map(parsec.TakeWhile(unicode.IsDigit), func(d string) string { return s + d })
		}
		// Left identity: Bind(Return(v), f) == f(v).
		v := rapid.StringMatching(`[ab]{0,2}`).Draw(t, "v")
		in1 := parsec.StartInput(parsec.NewStream(strings.NewReader(src)))
		in2 := parsec.StartInput(parsec.NewStream(strings.NewReader(src)))
		lv, lo, lok := observe(parsec.Bind(parsec.Return(v), f), in1)
		rv, ro, rok := observe(f(v), in2)
		if lv != rv || lo != ro || lok != rok {
			t.Fatalf("left identity: (%q,%d,%v) vs (%q,%d,%v)", lv, lo, lok, rv, ro, rok)
		}
		// Right identity: Bind(p, Return) == p.
		in3 := parsec.StartInput(parsec.NewStream(strings.NewReader(src)))
		in4 := parsec.StartInput(parsec.NewStream(strings.NewReader(src)))
		bv, bo, bok := observe(parsec.Bind(p, parsec.Return[string]), in3)
		pv, po, pok := observe(p, in4)
		if bv != pv || bo != po || bok != pok {
			t.Fatalf("right identity: (%q,%d,%v) vs (%q,%d,%v)", bv, bo, bok, pv, po, pok)
		}
	})
}

func TestOrAssociativity(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		p, q, r := genParser(t), genParser(t), genParser(t)
		src := genInput(t)
		in1 := parsec.StartInput(parsec.NewStream(strings.NewReader(src)))
		in2 := parsec.StartInput(parsec.NewStream(strings.NewReader(src)))
		lv, lo, lok := observe(parsec.Or(parsec.Or(p, q), r), in1)
		rv, ro, rok := observe(parsec.Or(p, parsec.Or(q, r)), in2)
		if lv != rv || lo != ro || lok != rok {
			t.Fatalf("Or assoc: (%q,%d,%v) vs (%q,%d,%v)", lv, lo, lok, rv, ro, rok)
		}
	})
}

func TestTryNeverConsumesOnFailure(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		p := genParser(t)
		src := genInput(t)
		in := parsec.StartInput(parsec.NewStream(strings.NewReader(src)))
		match := parsec.Try(p)(in)
		parsec.Fold(match, parsec.ReplyCases[string, struct{}]{
			ConsumedOk: func(string, parsec.Input) struct{} { return struct{}{} },
			EmptyOk:    func(string, parsec.Input) struct{} { return struct{}{} },
			ConsumedErr: func(parsec.ParseError) struct{} {
				t.Fatal("Try produced a consumed failure")
				return struct{}{}
			},
			EmptyErr: func(parsec.ParseError) struct{} { return struct{}{} },
		})
	})
}

func TestStreamingEqualsString(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		p := genParser(t)
		src := genInput(t)
		chunk := rapid.IntRange(1, 4).Draw(t, "chunk")
		inStr := parsec.StartInput(parsec.NewStream(strings.NewReader(src)))
		inChunk := parsec.StartInput(parsec.NewStream(&chunkReader{s: src, n: chunk}))
		sv, so, sok := observe(p, inStr)
		cv, co, cok := observe(p, inChunk)
		if sv != cv || so != co || sok != cok {
			t.Fatalf("chunk=%d: (%q,%d,%v) vs (%q,%d,%v)", chunk, sv, so, sok, cv, co, cok)
		}
	})
}

func TestManyMany1Agreement(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		lit := rapid.StringMatching(`[ab]{1,2}`).Draw(t, "lit")
		src := genInput(t)
		p := parsec.Try(parsec.Str(lit))
		many, _ := parsec.RunString(parsec.Map(parsec.Many(p), func(v []string) int { return len(v) }), src)
		many1, err1 := parsec.RunString(parsec.Map(parsec.Many1(p), func(v []string) int { return len(v) }), src)
		// Wherever Many1 succeeds, Many agrees; where Many sees zero,
		// Many1 fails.
		if err1 == nil && many1 != many {
			t.Fatalf("Many=%d Many1=%d", many, many1)
		}
		if err1 != nil && many != 0 {
			t.Fatalf("Many1 failed while Many matched %d", many)
		}
	})
}

func TestMultilinePositions(t *testing.T) {
	src := "aa\nbb\ncc"
	p := parsec.Then(parsec.Str("aa\nbb\n"), parsec.Rune('x'))
	_, err := parsec.RunString(p, src)
	if err == nil || !strings.Contains(err.Error(), "3:1") {
		t.Fatalf("position: %v", err)
	}
}
