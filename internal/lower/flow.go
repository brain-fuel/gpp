package lower

// Pass-1 lowering of pipelines and composition (v0.3.0). Every segment
// whose meaning is syntactic lowers to plain Go immediately; only bare
// segments — whose member-vs-function reading needs the piped value's
// type — become reserved undeclared-function carrier calls that the
// resolution fixpoint finishes. Compositions always become carriers (their
// operand signatures need types).

import (
	"fmt"
	"go/ast"
	"go/token"
	"strings"

	"goforge.dev/gpp/internal/diag"
	"goforge.dev/gpp/internal/syntax"
)

const (
	// BareCarrierPrefix marks a pipeline segment awaiting member-vs-
	// function resolution: __gpp_bare_Map(head, args…).
	BareCarrierPrefix = "__gpp_bare_"
	// SegCarrierPrefix marks a direct-callee segment awaiting the flowing
	// type (railway lifting): __gpp_seg1(head, callee, fixedArgs…) — the
	// digit is the piped value's insertion index among the final args.
	SegCarrierPrefix = "__gpp_seg"
	// DotCarrier wraps a dot-segment's receiver: __gpp_dot(head).Suffix…
	DotCarrier = "__gpp_dot"
	// ComposeCarrier marks a composition awaiting operand types:
	// __gpp_comp(f, g, …).
	ComposeCarrier = "__gpp_comp"
)

// FlowEdits lowers every outermost pipeline/composition in the file,
// except those inside match subjects (MatchSkeleton renders those via
// ExprText — its header edit covers the subject span).
func FlowEdits(f *syntax.File) ([]Edit, []diag.Diagnostic) {
	var edits []Edit
	var diags []diag.Diagnostic

	type span struct{ from, to int }
	var subjectSpans []span
	for _, m := range f.Matches {
		subjectSpans = append(subjectSpans, span{f.Offset(m.Subject.Pos()), f.Offset(m.Subject.End())})
	}
	inSubject := func(from, to int) bool {
		for _, s := range subjectSpans {
			if s.from <= from && to <= s.to {
				return true
			}
		}
		return false
	}

	pipes, composes := f.OutermostFlow()
	for _, p := range pipes {
		from, to := f.Offset(p.Bad.From), f.Offset(p.Bad.To)
		if inSubject(from, to) {
			continue
		}
		text, ds := PipeText(f, p)
		diags = append(diags, ds...)
		if len(ds) == 0 {
			edits = append(edits, Edit{Start: from, End: to, New: text})
		}
	}
	for _, c := range composes {
		from, to := f.Offset(c.Bad.From), f.Offset(c.Bad.To)
		if inSubject(from, to) {
			continue
		}
		text, ds := ComposeText(f, c)
		diags = append(diags, ds...)
		if len(ds) == 0 {
			edits = append(edits, Edit{Start: from, End: to, New: text})
		}
	}
	return edits, diags
}

// ExprText renders an expression's source text with any nested flow
// placeholders replaced by their lowered text.
func ExprText(f *syntax.File, e ast.Expr) (string, []diag.Diagnostic) {
	if bad, ok := e.(*ast.BadExpr); ok {
		if p, isPipe := f.PipeFor(bad); isPipe {
			return PipeText(f, p)
		}
		if c, isComp := f.ComposeFor(bad); isComp {
			return ComposeText(f, c)
		}
		return string(f.Src[f.Offset(e.Pos()):f.Offset(e.End())]), nil
	}
	// Replace outermost nested BadExprs within e's span, if any.
	var nested []*ast.BadExpr
	ast.Inspect(e, func(n ast.Node) bool {
		if bad, ok := n.(*ast.BadExpr); ok {
			nested = append(nested, bad)
			return false
		}
		return true
	})
	base := f.Offset(e.Pos())
	text := string(f.Src[base:f.Offset(e.End())])
	if len(nested) == 0 {
		return text, nil
	}
	var rel []Edit
	var diags []diag.Diagnostic
	for _, bad := range nested {
		btext, ds := ExprText(f, bad)
		diags = append(diags, ds...)
		rel = append(rel, Edit{Start: f.Offset(bad.From) - base, End: f.Offset(bad.To) - base, New: btext})
	}
	if len(diags) > 0 {
		return "", diags
	}
	out, err := Apply([]byte(text), rel)
	if err != nil {
		return "", []diag.Diagnostic{diag.At(f.Fset.Position(e.Pos()), "internal error: nested flow lowering: %v", err)}
	}
	return string(out), nil
}

// PipeText renders one pipeline as its lowered Go expression.
func PipeText(f *syntax.File, p *syntax.PipeExpr) (string, []diag.Diagnostic) {
	errAt := func(pos token.Pos, format string, args ...any) []diag.Diagnostic {
		return []diag.Diagnostic{diag.At(f.Fset.Position(pos), format, args...)}
	}
	if id, ok := p.Head.(*ast.Ident); ok && id.Name == "_" {
		return "", errAt(id.Pos(), "a pipeline cannot start with _")
	}
	cur, diags := ExprText(f, p.Head)
	if len(diags) > 0 {
		return "", diags
	}
	headNode := p.Head

	for _, st := range p.Stages {
		next, ds := f2Stage(f, st, cur, headNode)
		if len(ds) > 0 {
			return "", ds
		}
		cur = next
		headNode = nil // only the original head can need parens
	}
	return cur, nil
}

// f2Stage lowers one segment given the current value text.
func f2Stage(f *syntax.File, st *syntax.PipeStage, cur string, headNode ast.Expr) (string, []diag.Diagnostic) {
	errAt := func(pos token.Pos, format string, args ...any) []diag.Diagnostic {
		return []diag.Diagnostic{diag.At(f.Fset.Position(pos), format, args...)}
	}
	_ = headNode // parenthesization happens at resolve time (carrier args)

	// Dot-segment: the __gpp_dot marker wraps the receiver so the whole
	// suffix chain waits for the flowing type.
	if st.Dot.IsValid() {
		if ph := topLevelPlaceholder(st.Expr); ph != nil {
			return "", errAt(ph.Pos(), "a dot segment receives the piped value as its receiver; _ is not allowed here")
		}
		text, ds := ExprText(f, st.Expr)
		if len(ds) > 0 {
			return "", ds
		}
		return DotCarrier + "(" + cur + ")." + text, nil
	}

	switch seg := st.Expr.(type) {
	case *ast.CallExpr:
		return lowerCallSegment(f, st, seg, cur)
	case *ast.Ident:
		if seg.Name == "_" {
			return "", errAt(seg.Pos(), "a pipeline segment cannot be a bare _")
		}
		return BareCarrierPrefix + seg.Name + "(" + cur + ")", nil
	case *ast.SelectorExpr:
		text, ds := ExprText(f, seg)
		if len(ds) > 0 {
			return "", ds
		}
		return SegCarrierPrefix + "0(" + cur + ", " + text + ")", nil
	case *ast.IndexExpr, *ast.IndexListExpr:
		// Bare instantiated name (Map[string]) or indexed value (fs[0]):
		// carrier preserves the bracket text; resolution decides.
		if name, brackets, ok := indexedBareParts(f, st.Expr); ok {
			return BareCarrierPrefix + name + brackets + "(" + cur + ")", nil
		}
		text, ds := ExprText(f, st.Expr)
		if len(ds) > 0 {
			return "", ds
		}
		return SegCarrierPrefix + "0(" + cur + ", (" + text + "))", nil
	case *ast.BinaryExpr:
		switch seg.Op {
		case token.LAND, token.LOR, token.EQL, token.NEQ,
			token.LSS, token.LEQ, token.GTR, token.GEQ:
			return "", errAt(seg.OpPos,
				"pipeline stage is a %s expression; if you meant to compare the piped result, parenthesize the pipeline: (x |> f) %s …",
				opKind(seg.Op), seg.Op)
		}
		text, ds := ExprText(f, seg)
		if len(ds) > 0 {
			return "", ds
		}
		return SegCarrierPrefix + "0(" + cur + ", (" + text + "))", nil
	default:
		text, ds := ExprText(f, st.Expr)
		if len(ds) > 0 {
			return "", ds
		}
		return SegCarrierPrefix + "0(" + cur + ", (" + text + "))", nil
	}
}

// lowerCallSegment handles call-shaped segments: placeholder substitution,
// direct qualified calls, and bare carriers.
func lowerCallSegment(f *syntax.File, st *syntax.PipeStage, call *ast.CallExpr, cur string) (string, []diag.Diagnostic) {
	errAt := func(pos token.Pos, format string, args ...any) []diag.Diagnostic {
		return []diag.Diagnostic{diag.At(f.Fset.Position(pos), format, args...)}
	}
	// Placeholder slot?
	var placeholders []*ast.Ident
	for _, a := range call.Args {
		if id, ok := a.(*ast.Ident); ok && id.Name == "_" {
			placeholders = append(placeholders, id)
		}
	}
	if len(placeholders) > 1 {
		return "", errAt(placeholders[1].Pos(),
			"a pipeline segment must contain exactly one _; found %d (use a partial application outside the pipeline or a closure)", len(placeholders))
	}

	// Fixed args (placeholders excluded) and the piped value's insertion
	// index among the FINAL call arguments.
	insertAt := 0
	var fixed []string
	for i, a := range call.Args {
		if id, ok := a.(*ast.Ident); ok && id.Name == "_" {
			insertAt = i
			continue
		}
		text, ds := ExprText(f, a)
		if len(ds) > 0 {
			return "", ds
		}
		if call.Ellipsis.IsValid() && i == len(call.Args)-1 {
			text += "..."
		}
		fixed = append(fixed, text)
	}

	calleeBare, brackets, isBare := bareCallee(f, call.Fun)
	if isBare && len(placeholders) == 0 {
		insertion := cur
		if len(fixed) > 0 {
			insertion = cur + ", " + strings.Join(fixed, ", ")
		}
		return BareCarrierPrefix + calleeBare + brackets + "(" + insertion + ")", nil
	}

	calleeText, ds := ExprText(f, call.Fun)
	if len(ds) > 0 {
		return "", ds
	}
	switch call.Fun.(type) {
	case *ast.Ident, *ast.SelectorExpr, *ast.IndexExpr, *ast.IndexListExpr:
	default:
		calleeText = "(" + calleeText + ")"
	}
	parts := append([]string{cur, calleeText}, fixed...)
	return fmt.Sprintf("%s%d(%s)", SegCarrierPrefix, insertAt, strings.Join(parts, ", ")), nil
}

// bareCallee reports whether a callee is a bare identifier, possibly
// instantiated/indexed, returning the name and verbatim bracket text.
func bareCallee(f *syntax.File, fun ast.Expr) (name, brackets string, ok bool) {
	switch fn := fun.(type) {
	case *ast.Ident:
		return fn.Name, "", true
	case *ast.IndexExpr:
		if id, isID := fn.X.(*ast.Ident); isID {
			return id.Name, string(f.Src[f.Offset(fn.Lbrack):f.Offset(fn.Rbrack) + 1]), true
		}
	case *ast.IndexListExpr:
		if id, isID := fn.X.(*ast.Ident); isID {
			return id.Name, string(f.Src[f.Offset(fn.Lbrack):f.Offset(fn.Rbrack) + 1]), true
		}
	}
	return "", "", false
}

func indexedBareParts(f *syntax.File, e ast.Expr) (name, brackets string, ok bool) {
	return bareCallee(f, e)
}

// ComposeText renders a composition as its carrier call.
func ComposeText(f *syntax.File, c *syntax.ComposeExpr) (string, []diag.Diagnostic) {
	var parts []string
	for _, op := range c.Fns {
		text, ds := ExprText(f, op)
		if len(ds) > 0 {
			return "", ds
		}
		parts = append(parts, text)
	}
	return ComposeCarrier + "(" + strings.Join(parts, ", ") + ")", nil
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

// exprNeedsParen mirrors resolve's needsParen for selector prefixes.
func exprNeedsParen(e ast.Expr) bool {
	switch e.(type) {
	case *ast.Ident, *ast.SelectorExpr, *ast.IndexExpr, *ast.IndexListExpr,
		*ast.CallExpr, *ast.ParenExpr, *ast.CompositeLit, *ast.BasicLit:
		return false
	}
	return true
}

func opKind(op token.Token) string {
	switch op {
	case token.LAND, token.LOR:
		return "boolean"
	default:
		return "comparison"
	}
}
