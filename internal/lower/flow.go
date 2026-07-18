package lower

// Pass-1 lowering of pipelines and composition. Every segment lowers to a
// self-describing carrier (Engine A, v0.4.0): resolution collapses each
// stage once the flowing type is known, choosing direct or railway
// emission. Bare segments keep the v0.3 member/function carrier; composes
// carry per-link operator kinds.

import (
	"fmt"
	"go/ast"
	"go/token"
	"strings"

	"goforge.dev/gpp/internal/syntax"
)

const (
	// BareCarrierPrefix marks a pipeline segment awaiting member-vs-
	// function resolution: __gpp_bare_Map(head, args…).
	BareCarrierPrefix = "__gpp_bare_"
	// SegCarrierPrefix marks a direct-callee segment awaiting the flowing
	// type: __gpp_seg1(head, callee, fixedArgs…) — the digit is the piped
	// value's insertion index among the final args.
	SegCarrierPrefix = "__gpp_seg"
	// DotCarrier wraps a dot-segment's receiver: __gpp_dot(head).Suffix…
	DotCarrier = "__gpp_dot"
	// ComposeCarrier marks a one-track composition: __gpp_comp(f, g, …).
	ComposeCarrier = "__gpp_comp"
	// KleisliCarrierPrefix marks a mixed/railway composition with per-link
	// kinds encoded as letters: __gpp_kcomp_kc(f, g, h).
	KleisliCarrierPrefix = "__gpp_kcomp_"
)

// pipeTextCtx renders one pipeline through the hoister context.
func pipeTextCtx(h *Hoister, p *syntax.PipeExpr) (string, bool) {
	if id, ok := p.Head.(*ast.Ident); ok && id.Name == "_" {
		h.errAt(id.Pos(), "a pipeline cannot start with _")
		return "", false
	}
	cur, ok := h.render(p.Head)
	if !ok {
		return "", false
	}
	for _, st := range p.Stages {
		next, sok := h.stageText(st, cur)
		if !sok {
			return "", false
		}
		cur = next
	}
	return cur, true
}

// composeTextCtx renders one composition carrier through the hoister.
func composeTextCtx(h *Hoister, c *syntax.ComposeExpr) (string, bool) {
	var parts []string
	for _, op := range c.Fns {
		text, ok := h.render(op)
		if !ok {
			return "", false
		}
		parts = append(parts, text)
	}
	kleisli := false
	kinds := make([]byte, len(c.Ops))
	for i, k := range c.Ops {
		if k == syntax.ComposeKleisli {
			kleisli = true
			kinds[i] = 'k'
		} else {
			kinds[i] = 'c'
		}
	}
	if kleisli {
		return KleisliCarrierPrefix + string(kinds) + "(" + strings.Join(parts, ", ") + ")", true
	}
	return ComposeCarrier + "(" + strings.Join(parts, ", ") + ")", true
}

// stageText lowers one segment given the current value text. A stage-level
// `?` applies to the STAGE RESULT (`x |> parse?` tries parse(x)), so try
// suffixes on the segment unwrap first and re-wrap the rendered segment.
func (h *Hoister) stageText(st *syntax.PipeStage, cur string) (string, bool) {
	expr := st.Expr
	var tries []*syntax.TryExpr
	for {
		bad, isBad := expr.(*ast.BadExpr)
		if !isBad {
			break
		}
		t, isTry := h.f.TryFor(bad)
		if !isTry {
			break
		}
		tries = append(tries, t)
		expr = t.X
	}
	text, ok := h.segmentText(st, expr, cur)
	if !ok {
		return "", false
	}
	for i := len(tries) - 1; i >= 0; i-- {
		text = fmt.Sprintf("__gpp_try%d(%s)", h.tryIndex(tries[i]), text)
	}
	return text, true
}

// segmentText renders the segment expression proper.
func (h *Hoister) segmentText(st *syntax.PipeStage, expr ast.Expr, cur string) (string, bool) {
	// Dot-segment: the __gpp_dot marker wraps the receiver so the whole
	// suffix chain waits for the flowing type.
	if st.Dot.IsValid() {
		if ph := topLevelPlaceholder(expr); ph != nil {
			h.errAt(ph.Pos(), "a dot segment receives the piped value as its receiver; _ is not allowed here")
			return "", false
		}
		text, ok := h.render(expr)
		if !ok {
			return "", false
		}
		return DotCarrier + "(" + cur + ")." + text, true
	}

	switch seg := expr.(type) {
	case *ast.CallExpr:
		return h.callSegment(seg, cur)
	case *ast.Ident:
		if seg.Name == "_" {
			h.errAt(seg.Pos(), "a pipeline segment cannot be a bare _")
			return "", false
		}
		return BareCarrierPrefix + seg.Name + "(" + cur + ")", true
	case *ast.SelectorExpr:
		text, ok := h.render(seg)
		if !ok {
			return "", false
		}
		return SegCarrierPrefix + "0(" + cur + ", " + text + ")", true
	case *ast.IndexExpr, *ast.IndexListExpr:
		if name, brackets, ok := indexedBareParts(h.f, expr); ok {
			return BareCarrierPrefix + name + brackets + "(" + cur + ")", true
		}
		text, ok := h.render(expr)
		if !ok {
			return "", false
		}
		return SegCarrierPrefix + "0(" + cur + ", (" + text + "))", true
	case *ast.BinaryExpr:
		switch seg.Op {
		case token.LAND, token.LOR, token.EQL, token.NEQ,
			token.LSS, token.LEQ, token.GTR, token.GEQ:
			h.errAt(seg.OpPos,
				"pipeline stage is a %s expression; if you meant to compare the piped result, parenthesize the pipeline: (x |> f) %s …",
				opKind(seg.Op), seg.Op)
			return "", false
		}
		text, ok := h.render(seg)
		if !ok {
			return "", false
		}
		return SegCarrierPrefix + "0(" + cur + ", (" + text + "))", true
	default:
		text, ok := h.render(expr)
		if !ok {
			return "", false
		}
		return SegCarrierPrefix + "0(" + cur + ", (" + text + "))", true
	}
}

// callSegment handles call-shaped segments.
func (h *Hoister) callSegment(call *ast.CallExpr, cur string) (string, bool) {
	var placeholders []*ast.Ident
	for _, a := range call.Args {
		if id, ok := a.(*ast.Ident); ok && id.Name == "_" {
			placeholders = append(placeholders, id)
		}
	}
	if len(placeholders) > 1 {
		h.errAt(placeholders[1].Pos(),
			"a pipeline segment must contain exactly one _; found %d (use a partial application outside the pipeline or a closure)", len(placeholders))
		return "", false
	}

	insertAt := 0
	var fixed []string
	for i, a := range call.Args {
		if id, ok := a.(*ast.Ident); ok && id.Name == "_" {
			insertAt = i
			continue
		}
		text, ok := h.render(a)
		if !ok {
			return "", false
		}
		if call.Ellipsis.IsValid() && i == len(call.Args)-1 {
			text += "..."
		}
		fixed = append(fixed, text)
	}

	calleeBare, brackets, isBare := bareCallee(h.f, call.Fun)
	if isBare && len(placeholders) == 0 {
		insertion := cur
		if len(fixed) > 0 {
			insertion = cur + ", " + strings.Join(fixed, ", ")
		}
		return BareCarrierPrefix + calleeBare + brackets + "(" + insertion + ")", true
	}

	calleeText, ok := h.render(call.Fun)
	if !ok {
		return "", false
	}
	switch call.Fun.(type) {
	case *ast.Ident, *ast.SelectorExpr, *ast.IndexExpr, *ast.IndexListExpr:
	default:
		calleeText = "(" + calleeText + ")"
	}
	parts := append([]string{cur, calleeText}, fixed...)
	return fmt.Sprintf("%s%d(%s)", SegCarrierPrefix, insertAt, strings.Join(parts, ", ")), true
}

// bareCallee reports whether a callee is a bare identifier, possibly
// instantiated/indexed, returning the name and verbatim bracket text.
func bareCallee(f *syntax.File, fun ast.Expr) (name, brackets string, ok bool) {
	switch fn := fun.(type) {
	case *ast.Ident:
		return fn.Name, "", true
	case *ast.IndexExpr:
		if id, isID := fn.X.(*ast.Ident); isID {
			return id.Name, string(f.Src[f.Offset(fn.Lbrack) : f.Offset(fn.Rbrack)+1]), true
		}
	case *ast.IndexListExpr:
		if id, isID := fn.X.(*ast.Ident); isID {
			return id.Name, string(f.Src[f.Offset(fn.Lbrack) : f.Offset(fn.Rbrack)+1]), true
		}
	}
	return "", "", false
}

func indexedBareParts(f *syntax.File, e ast.Expr) (name, brackets string, ok bool) {
	return bareCallee(f, e)
}

// topLevelPlaceholder finds a `_` among a segment call's direct arguments.
func topLevelPlaceholder(e ast.Expr) *ast.Ident {
	call, ok := e.(*ast.CallExpr)
	if !ok {
		return nil
	}
	for _, a := range call.Args {
		if id, isID := a.(*ast.Ident); isID && id.Name == "_" {
			return id
		}
	}
	return nil
}

func opKind(op token.Token) string {
	switch op {
	case token.LAND, token.LOR:
		return "boolean"
	default:
		return "comparison"
	}
}
