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

	t.Run("v0.4 unclaimed forms keep stock errors", func(t *testing.T) {
		for _, expr := range []string{
			"a ? b : c", "f() ?", "a >= > b", "a >=>= b", "a >=>> b",
		} {
			stockErr, forkErr, ext := parseBoth(t, wrap(expr))
			if stockErr == nil {
				t.Errorf("%q: expected a stock parse error", expr)
				continue
			}
			if forkErr == nil || forkErr.Error() != stockErr.Error() {
				t.Errorf("%q: error parity broken:\nstock: %v\nfork:  %v", expr, stockErr, forkErr)
			}
			if ext != nil && (len(ext.Tries) > 0 || len(ext.Composes) > 0) {
				t.Errorf("%q: near-miss was claimed", expr)
			}
		}
		// Valid Go that must stay claim-free.
		for _, src := range []string{
			"package b\n\nfunc f(match, x int) int { return match + x }\n",
			"package b\n\nfunc f(match chan int) { match <- 1 }\n",
			"package b\n\nfunc try(x int) int { return x }\n\nfunc g() int { return try(1) }\n",
			"package b\n\nfunc f(a, b int) bool { return a >= b }\n",
		} {
			mode := stdparser.ParseComments | stdparser.SkipObjectResolution
			_, ext, err := forkparser.ParseFileExt(token.NewFileSet(), "b.go", []byte(src), forkparser.Mode(mode))
			if err != nil {
				t.Errorf("valid Go rejected: %v\n%s", err, src)
				continue
			}
			if len(ext.Tries)+len(ext.MatchExprs)+len(ext.IfExprs)+len(ext.SwitchExprs)+len(ext.Composes) > 0 {
				t.Errorf("valid Go claimed extensions:\n%s", src)
			}
		}
	})

	t.Run("v0.4 claimed forms", func(t *testing.T) {
		for _, tc := range []struct {
			expr                              string
			tries, ifs, switches, matchExprs int
		}{
			{"f()?", 1, 0, 0, 0},
			{"f()?.g()?", 2, 0, 0, 0},
			{"f(g()?)?", 2, 0, 0, 0},
			{"if c { a } else { b }", 0, 1, 0, 0},
			{"if a { 1 } else if b { 2 } else { 3 }", 0, 1, 0, 0},
			{"switch { default: 1 }", 0, 0, 1, 0},
			{"switch c { case a, b: 1\ndefault: 2 }", 0, 0, 1, 0},
			{"match c { case _: 1 }", 0, 0, 0, 1},
			{"if c { a } else { b }?", 1, 1, 0, 0},
		} {
			stockErr, forkErr, ext := parseBoth(t, wrap(tc.expr))
			if stockErr == nil {
				t.Errorf("%q: expected stock go/parser to reject this", tc.expr)
			}
			if forkErr != nil {
				t.Errorf("%q: fork failed: %v", tc.expr, forkErr)
				continue
			}
			if len(ext.Tries) != tc.tries || len(ext.IfExprs) != tc.ifs ||
				len(ext.SwitchExprs) != tc.switches || len(ext.MatchExprs) != tc.matchExprs {
				t.Errorf("%q: got tries=%d ifs=%d switches=%d matches=%d, want %d/%d/%d/%d",
					tc.expr, len(ext.Tries), len(ext.IfExprs), len(ext.SwitchExprs), len(ext.MatchExprs),
					tc.tries, tc.ifs, tc.switches, tc.matchExprs)
			}
		}
	})

	t.Run("kleisli kinds", func(t *testing.T) {
		_, forkErr, ext := parseBoth(t, wrap("f >=> g >>> h"))
		if forkErr != nil {
			t.Fatal(forkErr)
		}
		if len(ext.Composes) != 1 {
			t.Fatalf("composes=%d", len(ext.Composes))
		}
		ops := ext.Composes[0].Ops
		if len(ops) != 2 || ops[0] != forkparser.ComposeKleisli || ops[1] != forkparser.ComposeFn {
			t.Fatalf("ops=%v", ops)
		}
	})

	t.Run("complit guard", func(t *testing.T) {
		// An extension placeholder must never become a composite-literal
		// type: expect an error, never a silent CompositeLit parse.
		_, forkErr, _ := parseBoth(t, wrap("f()?{1}"))
		if forkErr == nil {
			t.Fatal("f()?{1} parsed silently")
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

// TestClassClaimBoundary pins the v0.5.0 class/instance claims: valid Go
// using `class`, `instance`, and `law` as ordinary identifiers is untouched
// (zero claims, error parity), while the claimed forms parse with the
// expected structure.
func TestClassClaimBoundary(t *testing.T) {
	t.Run("valid Go stays Go", func(t *testing.T) {
		for _, src := range []string{
			"package b\n\nvar class = 1\n",
			"package b\n\nvar instance = 2\n",
			"package b\n\nvar law = 3\n",
			"package b\n\ntype class struct{ law int }\n",
			"package b\n\ntype instance int\n",
			"package b\n\nfunc f() { instance := g(); _ = instance }\nfunc g() int { return 0 }\n",
			"package b\n\ntype T class // identifier type named class, no brace\n",
			"package b\n\nfunc f(class, law int) int { return class + law }\n",
		} {
			stockErr, forkErr, ext := parseBoth(t, src)
			if (stockErr == nil) != (forkErr == nil) {
				t.Errorf("%q: error presence mismatch:\nstock: %v\nfork:  %v", src, stockErr, forkErr)
				continue
			}
			if stockErr != nil && forkErr.Error() != stockErr.Error() {
				t.Errorf("%q: error parity broken:\nstock: %v\nfork:  %v", src, stockErr, forkErr)
			}
			if ext != nil && (len(ext.Classes) > 0 || len(ext.Instances) > 0) {
				t.Errorf("%q: valid Go was claimed", src)
			}
		}
	})

	t.Run("invalid instance-like Go keeps stock-shaped errors", func(t *testing.T) {
		// `instance` followed by a non-identifier is NOT claimed.
		for _, src := range []string{
			"package b\n\ninstance := 1\n",
			"package b\n\ninstance + 2\n",
		} {
			stockErr, forkErr, ext := parseBoth(t, src)
			if stockErr == nil || forkErr == nil {
				t.Errorf("%q: expected errors from both parsers (stock %v, fork %v)", src, stockErr, forkErr)
				continue
			}
			if forkErr.Error() != stockErr.Error() {
				t.Errorf("%q: error parity broken:\nstock: %v\nfork:  %v", src, stockErr, forkErr)
			}
			if ext != nil && len(ext.Instances) > 0 {
				t.Errorf("%q: near-miss was claimed", src)
			}
		}
	})

	t.Run("claimed forms parse with structure", func(t *testing.T) {
		src := `package b

type Magma[T any] class {
	Combine(a, b T) T
}

type Monoid[T any] class {
	Semigroup[T]
	pkg.UnitalMagma[T]
	Empty() T
	law LeftId(a T) { return Combine(Empty(), a) == a }
	LeftDiv(a, b T) T { return Combine(Invert(b), a) }
}

instance IntAdd Monoid[int] {
	Combine(a, b int) int { return a + b }
	Empty() int { return 0 }
}

instance SliceConcat[T any] Monoid[[]T] {
	Combine(a, b []T) []T { return append(a, b...) }
	Empty() []T { return nil }
}
`
		_, forkErr, ext := parseBoth(t, src)
		if forkErr != nil {
			t.Fatalf("fork parse: %v", forkErr)
		}
		if len(ext.Classes) != 2 || len(ext.Instances) != 2 {
			t.Fatalf("classes=%d instances=%d, want 2/2", len(ext.Classes), len(ext.Instances))
		}
		m := ext.Classes[1]
		if len(m.Members) != 5 {
			t.Fatalf("monoid members = %d, want 5", len(m.Members))
		}
		if m.Members[0].Embed == nil || m.Members[1].Embed == nil {
			t.Fatalf("embeds not recognized")
		}
		if m.Members[2].Name.Name != "Empty" || m.Members[2].Body != nil {
			t.Fatalf("op member wrong: %+v", m.Members[2])
		}
		if !m.Members[3].LawPos.IsValid() || m.Members[3].Body == nil {
			t.Fatalf("law member wrong")
		}
		if m.Members[4].Body == nil {
			t.Fatalf("default body missing")
		}
		if ext.Instances[0].TParams != nil || ext.Instances[1].TParams == nil {
			t.Fatalf("instance tparams wrong")
		}
	})

	t.Run("class error cases", func(t *testing.T) {
		for _, tc := range []struct{ src, want string }{
			{"package b\n\ntype M[T any] = class {\n\tCombine(a, b T) T\n}\n", "class declarations cannot be type aliases"},
			{"package b\n\ntype M[T any] class {\n\tlaw Assoc(a T)\n}\n", "a law requires a body"},
			{"package b\n\ninstance X Monoid {\n\tCombine(a, b int) int { return a }\n}\n", "an instance names a fully applied class"},
			{"package b\n\ninstance X Monoid[int] {\n\tCombine(a, b int) int\n}\n", "instance members must have a body"},
			{"package b\n\ntype M[T any] class {\n\t[]int\n}\n", "expected a class member"},
		} {
			_, forkErr, _ := parseBoth(t, tc.src)
			if forkErr == nil || !strings.Contains(forkErr.Error(), tc.want) {
				t.Errorf("%q: error = %v, want containing %q", tc.src, forkErr, tc.want)
			}
		}
	})
}

// TestDelegateClaimBoundary pins the v0.6.0 trailing-delegate claim: every
// valid Go reading of `delegate` in struct fields survives untouched.
func TestDelegateClaimBoundary(t *testing.T) {
	t.Run("valid Go stays Go", func(t *testing.T) {
		for _, src := range []string{
			"package b\n\ntype delegate int\n\ntype S struct {\n\tx delegate\n}\n",
			"package b\n\ntype delegate int\n\ntype S struct {\n\tStore delegate\n}\n",
			"package b\n\ntype S struct {\n\tinner string `json:\"i\"`\n}\n",
			"package b\n\ntype delegate int\n\nfunc f(delegate int) int { return delegate }\n",
		} {
			stockErr, forkErr, ext := parseBoth(t, src)
			if (stockErr == nil) != (forkErr == nil) {
				t.Errorf("%q: error presence mismatch:\nstock: %v\nfork:  %v", src, stockErr, forkErr)
				continue
			}
			if stockErr != nil && forkErr.Error() != stockErr.Error() {
				t.Errorf("%q: error parity broken:\nstock: %v\nfork:  %v", src, stockErr, forkErr)
			}
			if ext != nil && len(ext.Delegates) > 0 {
				t.Errorf("%q: valid Go was claimed", src)
			}
		}
	})

	t.Run("claimed forms", func(t *testing.T) {
		src := `package b

type S struct {
	inner Store delegate
	tagged Store delegate ` + "`json:\"t\"`" + `
	a, b Store delegate
	q pkg.Store delegate
	plain int
}
`
		_, forkErr, ext := parseBoth(t, src)
		if forkErr != nil {
			t.Fatalf("fork parse: %v", forkErr)
		}
		if len(ext.Delegates) != 4 {
			t.Fatalf("delegates = %d, want 4", len(ext.Delegates))
		}
		if ext.Delegates[1].Field.Tag == nil {
			t.Fatalf("tag after delegate not kept")
		}
		if len(ext.Delegates[2].Field.Names) != 2 {
			t.Fatalf("multi-name delegate field lost names")
		}
	})

	t.Run("existential variant tparams parse", func(t *testing.T) {
		src := `package b

type Row[T any] enum {
	Cell(v T)
	Packed[A fmt.Stringer, B error](x A, y A, e B) Row[T]
}
`
		_, forkErr, ext := parseBoth(t, src)
		if forkErr != nil {
			t.Fatalf("fork parse: %v", forkErr)
		}
		if len(ext.Enums) != 1 || len(ext.Enums[0].Variants) != 2 {
			t.Fatalf("enum shape wrong")
		}
		p := ext.Enums[0].Variants[1]
		if p.TParams == nil || len(p.TParams.List) != 2 {
			t.Fatalf("existential tparams not captured: %+v", p.TParams)
		}
		if p.Result == nil {
			t.Fatalf("result type lost after tparams")
		}
	})
}
