package parser_test

// The |> and >>> claims are adjacency-checked token sequences. Everything
// near-miss must remain byte-identical to stock go/parser errors; the
// claimed forms must parse with the expected extension counts. This test
// pins that boundary mechanically.

import (
	"go/ast"
	stdparser "go/parser"
	"go/token"
	"strings"
	"testing"

	forkparser "goforge.dev/gpp/internal/syntax/parser"
)

func parseBoth(t *testing.T, src string) (stockErr, forkErr error, ext *forkparser.Extensions) {
	t.Helper()
	mode := stdparser.ParseComments | stdparser.SkipObjectResolution
	_, stockErr = stdparser.ParseFile(token.NewFileSet(), "b.go", []byte(src), mode)
	_, ext, forkErr = forkparser.ParseFileExt(token.NewFileSet(), "b.go", []byte(src), forkparser.Mode(mode))
	return stockErr, forkErr, ext
}

func TestClaimBoundary(t *testing.T) {
	wrap := func(expr string) string {
		return "package b\n\nfunc f(a, b, c int) {\n\t_ = " + expr + "\n}\n"
	}

	t.Run("near-misses keep stock errors", func(t *testing.T) {
		for _, expr := range []string{
			"a | > b", "a ||> b", "a |>= b", "a |>> b",
			"a >> > b", "a >>>= b", "a >>>> b",
		} {
			stockErr, forkErr, ext := parseBoth(t, wrap(expr))
			if stockErr == nil {
				t.Errorf("%q: expected a stock parse error", expr)
				continue
			}
			if forkErr == nil || forkErr.Error() != stockErr.Error() {
				t.Errorf("%q: error parity broken:\nstock: %v\nfork:  %v", expr, stockErr, forkErr)
			}
			if ext != nil && (len(ext.Pipes) > 0 || len(ext.Composes) > 0) {
				t.Errorf("%q: near-miss was claimed", expr)
			}
		}
	})

	t.Run("claimed forms parse", func(t *testing.T) {
		for _, tc := range []struct {
			expr            string
			pipes, composes int
		}{
			{"a |> f", 1, 0},
			{"a |> f |> g", 1, 0},
			{"a >>> b", 0, 1},
			{"a >>> b >>> c", 0, 1},
			{"a |> f >>> g", 1, 1},
			{"a >>> b |> c", 1, 1},
			{"a + b |> f(c)", 1, 0},
			{"a |> .M(b).N(c)", 1, 0},
			{"a |> clamp(b, _, c)", 1, 0},
			{"a |> f(b |> g)", 2, 0},
		} {
			stockErr, forkErr, ext := parseBoth(t, wrap(tc.expr))
			if stockErr == nil {
				t.Errorf("%q: expected stock go/parser to reject this", tc.expr)
			}
			if forkErr != nil {
				t.Errorf("%q: fork failed: %v", tc.expr, forkErr)
				continue
			}
			if len(ext.Pipes) != tc.pipes || len(ext.Composes) != tc.composes {
				t.Errorf("%q: got %d pipes / %d composes, want %d / %d",
					tc.expr, len(ext.Pipes), len(ext.Composes), tc.pipes, tc.composes)
			}
		}
	})

	t.Run("structure facts", func(t *testing.T) {
		src := wrap("x |> f |> g(a) >>> h")
		_, forkErr, ext := parseBoth(t, src)
		if forkErr != nil {
			t.Fatal(forkErr)
		}
		if len(ext.Pipes) != 1 || len(ext.Composes) != 1 {
			t.Fatalf("pipes=%d composes=%d", len(ext.Pipes), len(ext.Composes))
		}
		pipe := ext.Pipes[0]
		if len(pipe.Stages) != 2 {
			t.Fatalf("stages=%d, want 2 (left-assoc flattening)", len(pipe.Stages))
		}
		// Second stage is g(a) >>> h — a compose chain placeholder.
		if _, isBad := pipe.Stages[1].Expr.(*ast.BadExpr); !isBad {
			t.Fatalf("stage 2 is %T, want *ast.BadExpr (compose)", pipe.Stages[1].Expr)
		}
		if head, ok := pipe.Head.(*ast.Ident); !ok || head.Name != "x" {
			t.Fatalf("head = %v", pipe.Head)
		}
	})

	t.Run("dot segment shapes", func(t *testing.T) {
		_, forkErr, ext := parseBoth(t, wrap("a |> .Map[string](f).Len()"))
		if forkErr != nil {
			t.Fatal(forkErr)
		}
		st := ext.Pipes[0].Stages[0]
		if !st.Dot.IsValid() {
			t.Fatal("dot position missing")
		}
		if !strings.Contains(exprShape(st.Expr), "CallExpr") {
			t.Fatalf("unexpected stage shape %s", exprShape(st.Expr))
		}
	})
}

func exprShape(e ast.Expr) string {
	switch x := e.(type) {
	case *ast.CallExpr:
		return "CallExpr(" + exprShape(x.Fun) + ")"
	case *ast.SelectorExpr:
		return "SelectorExpr(" + exprShape(x.X) + ")"
	case *ast.IndexExpr:
		return "IndexExpr(" + exprShape(x.X) + ")"
	case *ast.Ident:
		return "Ident"
	}
	return "other"
}
