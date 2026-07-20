package lower

// Engine B (v0.4.0): unified statement hoisting. Expression-position
// if/switch/match lower to statements injected before an anchor statement,
// with the expression site replaced by a type-deferred temp:
//
//	x := if c { e1 } else { e2 }
//	⇒ __gp_v0 := __gp_val0()          // prelude (temp typed at resolve)
//	  if c { __gp_v0 = e1 } else { __gp_v0 = e2 }
//	  x := __gp_v0
//
// Match expressions emit the v0.2 match SKELETON with arm assignments, so
// exhaustiveness, GADT filtering, and nested patterns come for free.
// Hoisted sites evaluate before the rest of their statement, in source
// order (documented language semantic).

import (
	"fmt"
	"go/ast"
	"go/token"
	"strings"

	"goforge.dev/goplus/internal/diag"
	"goforge.dev/goplus/internal/syntax"
)

// ValCarrierPrefix defers an expression-form temp's type to resolution:
// `__gp_v0 := __gp_val0()`.
const ValCarrierPrefix = "__gp_val"

// Hoister renders a file's pass-1 flow and expression-form lowerings.
type Hoister struct {
	f        *syntax.File
	valN     int // expression-form temp counter
	matchN   int // continues the file's match-skeleton numbering
	anchors  *anchorIndex
	diags    []diag.Diagnostic
	preludes []string // collected while rendering one outermost site
}

// NewHoister prepares pass-1 rendering; matchStmtCount seeds skeleton
// numbering past the statement matches.
func NewHoister(f *syntax.File, matchStmtCount int) *Hoister {
	return &Hoister{f: f, matchN: matchStmtCount, anchors: buildAnchorIndex(f)}
}

func (h *Hoister) errAt(pos token.Pos, format string, args ...any) {
	h.diags = append(h.diags, diag.At(h.f.Fset.Position(pos), format, args...))
}

// FileEdits lowers all match statements and outermost extension
// expressions, returning the pass-1 edits.
func (h *Hoister) FileEdits() ([]Edit, []diag.Diagnostic) {
	var edits []Edit

	// Match statements: surgical skeleton edits, subjects rendered with
	// prelude support (a pipeline or expression form in a subject hoists
	// before the match).
	for mi, m := range h.f.Matches {
		h.preludes = nil
		subj, ok := h.render(m.Subject)
		if !ok {
			continue
		}
		skeleton := skeletonEdits(h.f, m, mi, subj)
		if len(h.preludes) > 0 {
			at := h.lineStart(h.f.Offset(m.Match))
			edits = append(edits, Edit{Start: at, End: at, New: strings.Join(h.preludes, "\n") + "\n"})
		}
		edits = append(edits, skeleton...)
	}

	// Outermost extension expressions (pipes, composes, tries handled by
	// their carriers; if/switch/match expressions hoist).
	subjectSpan := h.subjectSpans()
	for _, bad := range h.f.OutermostExt() {
		from, to := h.f.Offset(bad.From), h.f.Offset(bad.To)
		if subjectSpan(from, to) {
			continue // rendered by the enclosing match's subject
		}
		h.preludes = nil
		text, ok := h.render(bad)
		if !ok {
			continue
		}
		if len(h.preludes) > 0 {
			if !h.checkHoistPosition(bad) {
				continue
			}
			anchor, aok := h.anchors.anchorFor(h.f, from, to)
			if !aok {
				h.errAt(bad.From, "expression if/switch/match and ? need an enclosing statement; use an init function for package-level values")
				continue
			}
			edits = append(edits, Edit{Start: anchor, End: anchor, New: strings.Join(h.preludes, "\n") + "\n"})
		}
		edits = append(edits, Edit{Start: from, End: to, New: text})
	}
	return edits, h.diags
}

func (h *Hoister) subjectSpans() func(from, to int) bool {
	type span struct{ from, to int }
	var spans []span
	for _, m := range h.f.Matches {
		spans = append(spans, span{h.f.Offset(m.Subject.Pos()), h.f.Offset(m.Subject.End())})
	}
	return func(from, to int) bool {
		for _, s := range spans {
			if s.from <= from && to <= s.to {
				return true
			}
		}
		return false
	}
}

func (h *Hoister) lineStart(off int) int {
	for off > 0 && h.f.Src[off-1] != '\n' {
		off--
	}
	return off
}

// render produces the replacement text for an expression, collecting
// hoisted preludes on the way. ok=false when diagnostics were emitted.
func (h *Hoister) render(e ast.Expr) (string, bool) {
	if bad, isBad := e.(*ast.BadExpr); isBad {
		if p, isPipe := h.f.PipeFor(bad); isPipe {
			return h.renderPipe(p)
		}
		if c, isComp := h.f.ComposeFor(bad); isComp {
			return h.renderCompose(c)
		}
		if t, isTry := h.f.TryFor(bad); isTry {
			return h.renderTry(t)
		}
		if ie, isIf := h.f.IfFor(bad); isIf {
			return h.renderIfExpr(ie)
		}
		if se, isSw := h.f.SwitchExprFor(bad); isSw {
			return h.renderSwitchExpr(se)
		}
		if me, isMe := h.f.MatchExprFor(bad); isMe {
			return h.renderMatchExpr(me)
		}
		return string(h.f.Src[h.f.Offset(e.Pos()):h.f.Offset(e.End())]), true
	}
	// Stock expression: splice nested extension placeholders.
	var nested []*ast.BadExpr
	ast.Inspect(e, func(n ast.Node) bool {
		if bad, isBad := n.(*ast.BadExpr); isBad {
			nested = append(nested, bad)
			return false
		}
		return true
	})
	base := h.f.Offset(e.Pos())
	text := string(h.f.Src[base:h.f.Offset(e.End())])
	if len(nested) == 0 {
		return text, true
	}
	var rel []Edit
	for _, bad := range nested {
		btext, ok := h.render(bad)
		if !ok {
			return "", false
		}
		rel = append(rel, Edit{Start: h.f.Offset(bad.From) - base, End: h.f.Offset(bad.To) - base, New: btext})
	}
	out, err := Apply([]byte(text), rel)
	if err != nil {
		h.errAt(e.Pos(), "internal error: nested lowering: %v", err)
		return "", false
	}
	return string(out), true
}

// renderTry emits the pass-1 try carrier (resolution finishes it).
func (h *Hoister) renderTry(t *syntax.TryExpr) (string, bool) {
	inner, ok := h.render(t.X)
	if !ok {
		return "", false
	}
	return fmt.Sprintf("__gp_try%d(%s)", h.tryIndex(t), inner), true
}

// tryIndex is a try's stable pass-1 number: its index in the file's Tries.
func (h *Hoister) tryIndex(t *syntax.TryExpr) int {
	for i, cand := range h.f.Tries {
		if cand == t {
			return i
		}
	}
	return 0
}

// renderIfExpr hoists an if expression.
func (h *Hoister) renderIfExpr(e *syntax.IfExpr) (string, bool) {
	temp := h.newTemp()
	var b strings.Builder
	cur := e
	first := true
	for {
		before := len(h.preludes)
		cond, ok := h.render(cur.Cond)
		if !ok {
			return "", false
		}
		if !first && len(h.preludes) > before {
			h.errAt(cur.Cond.Pos(), "an expression if/switch/match cannot appear in an else-if condition; it would hoist before the whole chain and always evaluate — nest the if instead")
			return "", false
		}
		thenText, ok := h.renderArmAssign(temp, cur.Then)
		if !ok {
			return "", false
		}
		kw := "if"
		if !first {
			kw = " else if"
		}
		fmt.Fprintf(&b, "%s %s {\n%s\n}", kw, cond, thenText)
		first = false
		if cur.ElseIf != nil {
			cur = cur.ElseIf
			continue
		}
		if cur.Else == nil {
			h.errAt(e.If, "an expression if must have an else arm")
			return "", false
		}
		elseText, ok := h.renderArmAssign(temp, cur.Else)
		if !ok {
			return "", false
		}
		fmt.Fprintf(&b, " else {\n%s\n}", elseText)
		break
	}
	h.preludes = append(h.preludes, b.String())
	return temp, true
}

// renderSwitchExpr hoists a switch expression.
func (h *Hoister) renderSwitchExpr(e *syntax.SwitchExpr) (string, bool) {
	hasDefault := false
	for _, arm := range e.Arms {
		if arm.Values == nil {
			hasDefault = true
		}
	}
	if !hasDefault {
		h.errAt(e.Switch, "an expression switch must have a default arm")
		return "", false
	}
	temp := h.newTemp()
	var b strings.Builder
	b.WriteString("switch ")
	if e.Tag != nil {
		tag, ok := h.render(e.Tag)
		if !ok {
			return "", false
		}
		b.WriteString(tag + " ")
	}
	b.WriteString("{\n")
	for _, arm := range e.Arms {
		if arm.Values == nil {
			b.WriteString("default:\n")
		} else {
			var vals []string
			for _, v := range arm.Values {
				before := len(h.preludes)
				vt, ok := h.render(v)
				if !ok {
					return "", false
				}
				if len(h.preludes) > before {
					h.errAt(v.Pos(), "an expression if/switch/match cannot appear in a case value; case values evaluate in order only until one matches")
					return "", false
				}
				vals = append(vals, vt)
			}
			fmt.Fprintf(&b, "case %s:\n", strings.Join(vals, ", "))
		}
		armText, ok := h.renderArmAssign(temp, arm.Value)
		if !ok {
			return "", false
		}
		b.WriteString(armText + "\n")
	}
	b.WriteString("}")
	h.preludes = append(h.preludes, b.String())
	return temp, true
}

// renderMatchExpr hoists a match expression as a v0.2 match skeleton
// whose arms assign the temp — the whole match machinery applies.
func (h *Hoister) renderMatchExpr(e *syntax.MatchExpr) (string, bool) {
	temp := h.newTemp()
	subj, ok := h.render(e.Subject)
	if !ok {
		return "", false
	}
	idx := h.matchN
	h.matchN++
	var b strings.Builder
	fmt.Fprintf(&b, "switch __gp_m%d := any(%s).(type) {\n", idx, subj)
	for _, arm := range e.Arms {
		patStart := arm.Pattern.Pos()
		if arm.Binder != nil {
			patStart = arm.Binder.Pos()
		}
		pattern := string(h.f.Src[h.f.Offset(patStart):h.f.Offset(arm.Colon)])
		fmt.Fprintf(&b, "case nil:\n%s%s\n", PatternCarrier, strings.TrimSpace(pattern))
		armText, ok := h.renderArmAssign(temp, arm.Value)
		if !ok {
			return "", false
		}
		b.WriteString(armText + "\n")
	}
	b.WriteString("}")
	h.preludes = append(h.preludes, b.String())
	return temp, true
}

// renderArmAssign renders one arm expression as `temp = <expr>`, with any
// nested hoists (lazily) placed inside the arm before the assignment.
func (h *Hoister) renderArmAssign(temp string, arm ast.Expr) (string, bool) {
	outer := h.preludes
	h.preludes = nil
	text, ok := h.render(arm)
	if !ok {
		h.preludes = outer
		return "", false
	}
	inner := h.preludes
	h.preludes = outer
	assign := temp + " = " + text
	if len(inner) > 0 {
		return strings.Join(inner, "\n") + "\n" + assign, true
	}
	return assign, true
}

func (h *Hoister) newTemp() string {
	n := h.valN
	h.valN++
	h.preludes = append(h.preludes, fmt.Sprintf("__gp_v%d := %s%d()", n, ValCarrierPrefix, n))
	return fmt.Sprintf("__gp_v%d", n)
}

// renderPipe/renderCompose delegate to the v0.3 renderers, threading
// nested hoists through this context.
func (h *Hoister) renderPipe(p *syntax.PipeExpr) (string, bool) {
	return pipeTextCtx(h, p)
}

func (h *Hoister) renderCompose(c *syntax.ComposeExpr) (string, bool) {
	return composeTextCtx(h, c)
}

// ── Anchor discovery ───────────────────────────────────────────────────────

// anchorIndex records the byte spans of every statement that sits directly
// in a statement list — the legal insertion points — including match-arm
// bodies from the side tables, plus the parent links needed to check that
// a hoisted site's position admits statement insertion.
type anchorIndex struct {
	stmts   []stmtSpan
	parents map[ast.Node]ast.Node
	direct  map[ast.Node]bool // statements directly in a statement list
}

type stmtSpan struct{ from, to int }

func buildAnchorIndex(f *syntax.File) *anchorIndex {
	idx := &anchorIndex{parents: map[ast.Node]ast.Node{}, direct: map[ast.Node]bool{}}
	add := func(list []ast.Stmt) {
		for _, s := range list {
			idx.direct[s] = true
			idx.stmts = append(idx.stmts, stmtSpan{f.Offset(s.Pos()), f.Offset(s.End())})
		}
	}
	visit := func(root ast.Node) {
		var stack []ast.Node
		ast.Inspect(root, func(n ast.Node) bool {
			if n == nil {
				stack = stack[:len(stack)-1]
				return false
			}
			if len(stack) > 0 {
				idx.parents[n] = stack[len(stack)-1]
			}
			stack = append(stack, n)
			switch b := n.(type) {
			case *ast.BlockStmt:
				add(b.List)
			case *ast.CaseClause:
				add(b.Body)
			case *ast.CommClause:
				add(b.Body)
			}
			return true
		})
	}
	visit(f.AST)
	for _, m := range f.Matches {
		visit(m.Subject)
		for _, c := range m.Cases {
			add(c.Body)
			for _, s := range c.Body {
				visit(s)
			}
		}
	}
	return idx
}

// checkHoistPosition walks up from a hoisted site checking each position
// on the way to its anchor statement. Positions that would change when
// the site evaluates — conditionally-evaluated or repeatedly-evaluated
// contexts — are hard errors.
func (h *Hoister) checkHoistPosition(bad *ast.BadExpr) bool {
	var n ast.Node = bad
	for {
		p, ok := h.anchors.parents[n]
		if !ok {
			return true // reached a root; package level is D19'd by anchorFor
		}
		switch pp := p.(type) {
		case *ast.ForStmt:
			if n == pp.Cond || n == pp.Post {
				h.errAt(bad.From, "an expression if/switch/match cannot appear in a for condition or post statement; it would hoist outside the loop and evaluate only once")
				return false
			}
		case *ast.IfStmt:
			if n == pp.Cond {
				if gp, isIf := h.anchors.parents[p].(*ast.IfStmt); isIf && gp.Else == p {
					h.errAt(bad.From, "an expression if/switch/match cannot appear in an else-if condition; it would hoist before the whole chain and always evaluate — nest the if statement instead")
					return false
				}
			}
		case *ast.BinaryExpr:
			if (pp.Op == token.LAND || pp.Op == token.LOR) && n == pp.Y {
				h.errAt(bad.From, "an expression if/switch/match cannot appear on the right side of %s; it would hoist before the statement and always evaluate — use an if statement instead", pp.Op)
				return false
			}
		case *ast.AssignStmt:
			for _, l := range pp.Lhs {
				if l == n {
					h.errAt(bad.From, "an expression if/switch/match cannot appear on the left side of an assignment")
					return false
				}
			}
		case *ast.CaseClause:
			for _, v := range pp.List {
				if v == n {
					h.errAt(bad.From, "an expression if/switch/match cannot appear in a case value; case values evaluate in order only until one matches")
					return false
				}
			}
		case *ast.CommClause:
			if n == pp.Comm {
				h.errAt(bad.From, "an expression if/switch/match cannot appear in a select communication clause")
				return false
			}
		}
		if h.anchors.direct[p] {
			return true
		}
		n = p
	}
}

// anchorFor returns the line-start offset of the innermost anchor
// statement containing [from,to).
func (a *anchorIndex) anchorFor(f *syntax.File, from, to int) (int, bool) {
	best := -1
	bestSize := 1 << 62
	for _, s := range a.stmts {
		if s.from <= from && to <= s.to && s.to-s.from < bestSize {
			best = s.from
			bestSize = s.to - s.from
		}
	}
	if best < 0 {
		return 0, false
	}
	for best > 0 && f.Src[best-1] != '\n' {
		best--
	}
	return best, true
}
