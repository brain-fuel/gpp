package parser_test

import (
	"go/token"
	"testing"

	forkparser "goforge.dev/goplus/internal/syntax/parser"
)

const goplusSrc = `package p

type Shape enum {
	// Circle is round.
	Circle(r float64)
	Rect(w, h float64)
	Point
}

type Expr[T any] enum {
	Lit(v int) Expr[int]
	If(c Expr[bool], t, e Expr[T])
}

func area(s Shape) float64 {
	var a float64
	match s {
	case Circle(r):
		a = 3.14 * r * r
	case c := Rect(w, _):
		a = w * w
		_ = c
		match s {
		case Point:
			a = 0
		case _:
		}
	case Point:
		a = 0
	}
	return a
}

func superset() {
	match := 5
	match++
	_ = match
}
`

func TestGoplusSmoke(t *testing.T) {
	fset := token.NewFileSet()
	f, ext, err := forkparser.ParseFileExt(fset, "p.gp", []byte(goplusSrc), forkparser.ParseComments|forkparser.SkipObjectResolution)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	if f == nil || len(ext.Enums) != 2 {
		t.Fatalf("enums = %d, want 2", len(ext.Enums))
	}
	sh := ext.Enums[0]
	if sh.Spec.Name.Name != "Shape" || len(sh.Variants) != 3 {
		t.Fatalf("Shape variants = %d", len(sh.Variants))
	}
	if sh.Variants[0].Doc == nil {
		t.Fatal("Circle doc comment lost")
	}
	ex := ext.Enums[1]
	if ex.Variants[0].Result == nil || ex.Variants[1].Result != nil {
		t.Fatalf("GADT result types wrong: Lit=%v If=%v", ex.Variants[0].Result, ex.Variants[1].Result)
	}
	if len(ext.Matches) != 2 {
		t.Fatalf("matches = %d, want 2 (pre-order)", len(ext.Matches))
	}
	outer := ext.Matches[0]
	if len(outer.Cases) != 3 {
		t.Fatalf("outer cases = %d", len(outer.Cases))
	}
	if outer.Cases[1].Binder == nil || outer.Cases[1].Binder.Name != "c" {
		t.Fatal("binder lost")
	}
	pos := fset.Position(outer.Cases[0].Pattern.Pos())
	if pos.Line != 18 {
		t.Fatalf("pattern position line = %d, want 18", pos.Line)
	}
}
