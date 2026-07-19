// G++ grammar hooks. This file is gpp's own (not vendored). The vendored
// parser calls into it from five marked hunks; everything else lives here.
package parser

import (
	"fmt"
	"go/ast"
	"go/token"
)

// ── Raw-token lookahead ────────────────────────────────────────────────────
//
// The stock parser is strictly LL(1). Contextual keywords need one extra
// token of lookahead, so we interpose a replay buffer between next0 and the
// scanner. Buffered tokens (comments included) replay through next0's
// normal path, keeping doc-comment collection intact.

type aheadTok struct {
	pos token.Pos
	tok token.Token
	lit string
}

func (p *parser) rawScan() (token.Pos, token.Token, string) {
	if len(p.ahead) > 0 {
		t := p.ahead[0]
		p.ahead = p.ahead[1:]
		return t.pos, t.tok, t.lit
	}
	return p.scanner.Scan()
}

// peekNonComment returns the next non-comment token after the current one,
// without consuming anything.
func (p *parser) peekNonComment() token.Token {
	return p.peekNonCommentTok().tok
}

// peekNonCommentTok is the position-aware peek (needed by the adjacency
// checks for |> and >>>).
func (p *parser) peekNonCommentTok() aheadTok {
	for _, t := range p.ahead {
		if t.tok != token.COMMENT {
			return t
		}
	}
	for {
		pos, tok, lit := p.scanner.Scan()
		p.ahead = append(p.ahead, aheadTok{pos, tok, lit})
		if tok != token.COMMENT {
			return aheadTok{pos, tok, lit}
		}
	}
}

// ── Enum declarations ──────────────────────────────────────────────────────

// parseTypeSpecType parses the Type of a type spec, recognizing the G++
// `enum { … }` and `class { … }` forms via contextual keywords.
func (p *parser) parseTypeSpecType(spec *ast.TypeSpec) {
	if p.tok == token.IDENT && p.lit == "enum" && p.peekNonComment() == token.LBRACE {
		p.parseEnumType(spec)
		return
	}
	if p.tok == token.IDENT && p.lit == "class" && p.peekNonComment() == token.LBRACE {
		p.parseClassType(spec)
		return
	}
	spec.Type = p.parseType()
}

func (p *parser) parseEnumType(spec *ast.TypeSpec) {
	if spec.Assign.IsValid() {
		p.error(spec.Assign, "enum declarations cannot be type aliases")
	}
	decl := &EnumDecl{Spec: spec, EnumPos: p.pos}
	p.next() // consume `enum`
	decl.Lbrace = p.expect(token.LBRACE)
	for p.tok != token.RBRACE && p.tok != token.EOF {
		decl.Variants = append(decl.Variants, p.parseVariant())
	}
	decl.Rbrace = p.expect(token.RBRACE)
	spec.Type = &ast.BadExpr{From: decl.EnumPos, To: decl.Rbrace + 1}
	p.ext.Enums = append(p.ext.Enums, decl)
}

func (p *parser) parseVariant() *Variant {
	v := &Variant{Doc: p.leadComment}
	v.Name = p.parseIdent()
	if p.tok == token.LBRACK {
		v.TParams = p.parseTypeParameters()
	}
	if p.tok == token.LPAREN {
		v.Params = p.parseParameters(false)
		for _, f := range v.Params.List {
			if len(f.Names) == 0 {
				p.error(f.Type.Pos(), "enum variant fields must be named")
			}
			if _, ok := f.Type.(*ast.Ellipsis); ok {
				p.error(f.Type.Pos(), "enum variant fields cannot be variadic")
			}
		}
	}
	// Optional GADT result type: anything before the terminating semicolon.
	if p.tok != token.SEMICOLON && p.tok != token.RBRACE && p.tok != token.EOF {
		v.Result = p.parseType()
	}
	v.Comment = p.expectSemi()
	return v
}

// ── Class and instance declarations (v0.5.0) ───────────────────────────────

// parseClassType parses `class { … }` in a type spec's type position. The
// claim is a strict superset: in that position `class` followed by `{` can
// only be an identifier type followed by a block, which is never valid Go.
func (p *parser) parseClassType(spec *ast.TypeSpec) {
	if spec.Assign.IsValid() {
		p.error(spec.Assign, "class declarations cannot be type aliases")
	}
	decl := &ClassDecl{Spec: spec, ClassPos: p.pos}
	p.next() // consume `class`
	decl.Lbrace = p.expect(token.LBRACE)
	for p.tok != token.RBRACE && p.tok != token.EOF {
		if m := p.parseClassMember(); m != nil {
			decl.Members = append(decl.Members, m)
		}
	}
	decl.Rbrace = p.expect(token.RBRACE)
	spec.Type = &ast.BadExpr{From: decl.ClassPos, To: decl.Rbrace + 1}
	p.ext.Classes = append(p.ext.Classes, decl)
}

// parseClassMember parses one embed, operation, or law. Disambiguation is
// local to the claimed body: `law` + identifier begins a law; identifier +
// `(` begins an operation; anything else is an embedded class reference.
func (p *parser) parseClassMember() *ClassMember {
	m := &ClassMember{Doc: p.leadComment}
	if p.tok == token.IDENT && p.lit == "law" && p.peekNonComment() == token.IDENT {
		m.LawPos = p.pos
		p.next() // consume `law`
		m.Name = p.parseIdent()
		m.Params = p.parseParameters(false)
		if p.tok != token.LBRACE {
			p.error(p.pos, "a law requires a body")
			p.advanceClassMember()
			return nil
		}
		m.Body = p.parseBody()
		m.Comment = p.expectSemi()
		return m
	}
	if p.tok == token.IDENT && p.peekNonComment() == token.LPAREN {
		m.Name = p.parseIdent()
		m.Params = p.parseParameters(false)
		if p.tok != token.LBRACE && p.tok != token.SEMICOLON && p.tok != token.RBRACE && p.tok != token.EOF {
			m.Result = p.parseType()
		}
		if p.tok == token.LBRACE {
			m.Body = p.parseBody() // default implementation
		}
		m.Comment = p.expectSemi()
		return m
	}
	// Embedded class reference: Semigroup[T] or pkg.Semigroup[T].
	embed := p.parseType()
	if !validClassRef(embed, false) {
		p.error(embed.Pos(), "expected a class member: an embedded class, an operation, or a law")
		p.advanceClassMember()
		return nil
	}
	m.Embed = embed
	m.Comment = p.expectSemi()
	return m
}

// advanceClassMember skips to the next member boundary after an error.
func (p *parser) advanceClassMember() {
	for p.tok != token.SEMICOLON && p.tok != token.RBRACE && p.tok != token.EOF {
		p.next()
	}
	if p.tok == token.SEMICOLON {
		p.next()
	}
}

// validClassRef reports whether e has the shape of a class reference:
// an identifier or selector, with type arguments iff instantiated is
// required (instance heads must be applied; embeds may name the tparam).
func validClassRef(e ast.Expr, needArgs bool) bool {
	switch t := e.(type) {
	case *ast.Ident:
		return !needArgs
	case *ast.SelectorExpr:
		_, ok := t.X.(*ast.Ident)
		return ok && !needArgs
	case *ast.IndexExpr:
		return validClassRef(t.X, false)
	case *ast.IndexListExpr:
		return validClassRef(t.X, false)
	}
	return false
}

// parseInstanceDecl parses a top-level
// `instance Name [TParams] Class[Args] { … }` declaration. Claimed via the
// parseDecl hunk: no valid Go declaration begins with an identifier, so the
// claim is trivially a strict superset.
func (p *parser) parseInstanceDecl() ast.Decl {
	d := &InstanceDecl{Doc: p.leadComment, InstancePos: p.pos}
	p.next() // consume `instance`
	d.Name = p.parseIdent()
	if p.tok == token.LBRACK {
		d.TParams = p.parseTypeParameters()
	}
	d.Class = p.parseType()
	if !validClassRef(d.Class, true) {
		p.error(d.Class.Pos(), "an instance names a fully applied class; write Monoid[int]")
	}
	d.Lbrace = p.expect(token.LBRACE)
	for p.tok != token.RBRACE && p.tok != token.EOF {
		if m := p.parseInstanceMember(); m != nil {
			d.Members = append(d.Members, m)
		}
	}
	d.Rbrace = p.expect(token.RBRACE)
	p.expectSemi()
	d.Decl = &ast.BadDecl{From: d.InstancePos, To: d.Rbrace + 1}
	p.ext.Instances = append(p.ext.Instances, d)
	return d.Decl
}

// parseInstanceMember parses one operation implementation.
func (p *parser) parseInstanceMember() *InstanceMember {
	m := &InstanceMember{Doc: p.leadComment}
	if p.tok != token.IDENT {
		p.error(p.pos, "expected an operation implementation")
		p.advanceClassMember()
		return nil
	}
	m.Name = p.parseIdent()
	if p.tok != token.LPAREN {
		p.error(p.pos, "expected an operation's parameters")
		p.advanceClassMember()
		return nil
	}
	m.Params = p.parseParameters(false)
	if p.tok != token.LBRACE && p.tok != token.SEMICOLON && p.tok != token.RBRACE && p.tok != token.EOF {
		m.Result = p.parseType()
	}
	if p.tok != token.LBRACE {
		p.error(p.pos, "instance members must have a body")
		p.advanceClassMember()
		return nil
	}
	m.Body = p.parseBody()
	m.Comment = p.expectSemi()
	return m
}

// ── Match statements ───────────────────────────────────────────────────────

// matchClaims reports whether a token immediately after statement-position
// `match` begins a match subject. Every excluded token keeps its valid-Go
// meaning (strict superset):
//
//	(    call match(x)              [    index/instantiation match[i]
//	{    composite literal match{}   .    selector match.f
//	<-   send match <- ch            = := , ++ -- etc.  assignment/inc
//	:    label match:                } ; EOF  bare expression statement
//
// Claimed tokens (identifier, literal, composite type keywords, unary
// operators other than <-) can never continue a valid Go statement that
// begins with a plain identifier — two operands in a row, or an identifier
// followed by a non-call expression, is not legal Go.
func matchClaims(tok token.Token) bool {
	switch tok {
	case token.IDENT, token.INT, token.FLOAT, token.IMAG, token.CHAR, token.STRING,
		token.FUNC, token.STRUCT, token.MAP, token.CHAN, token.INTERFACE,
		token.ADD, token.SUB, token.MUL, token.AND, token.XOR, token.NOT:
		return true
	}
	return false
}

func (p *parser) parseMatchStmt() ast.Stmt {
	m := &MatchStmt{Match: p.pos}
	// Pre-order registration: nested matches parsed inside arm bodies land
	// after their enclosing match.
	p.ext.Matches = append(p.ext.Matches, m)

	p.next() // consume `match`
	prevLev := p.exprLev
	p.exprLev = -1 // like a switch tag: no top-level composite literals
	m.Subject = p.parseRhs()
	p.exprLev = prevLev
	m.Lbrace = p.expect(token.LBRACE)
	for p.tok == token.CASE || p.tok == token.DEFAULT {
		m.Cases = append(m.Cases, p.parseMatchCase())
	}
	m.Rbrace = p.expect(token.RBRACE)
	p.expectSemi()

	m.Stmt = &ast.BadStmt{From: m.Match, To: m.Rbrace + 1}
	return m.Stmt
}

func (p *parser) parseMatchCase() *CaseClause {
	cc := &CaseClause{Case: p.pos}
	if p.tok == token.DEFAULT {
		p.error(p.pos, "match statements do not have a default case; use 'case _:'")
		p.next()
		cc.Pattern = &WildcardPattern{UnderscorePos: cc.Case}
		cc.Colon = p.expect(token.COLON)
		cc.Body = p.parseStmtList()
		return cc
	}
	p.expect(token.CASE)
	if p.tok == token.IDENT && p.peekNonComment() == token.DEFINE {
		if p.lit == "_" {
			p.error(p.pos, "cannot bind to _; name the binder or drop it")
		}
		cc.Binder = p.parseIdent()
		cc.Define = p.pos
		p.next() // consume :=
		if p.tok == token.IDENT && p.lit == "_" {
			p.error(p.pos, "cannot bind a wildcard pattern")
		}
	}
	cc.Pattern = p.parsePattern()
	cc.Colon = p.expect(token.COLON)
	cc.Body = p.parseStmtList()
	return cc
}

func (p *parser) parsePattern() Pattern {
	if p.tok == token.IDENT && p.lit == "_" {
		w := &WildcardPattern{UnderscorePos: p.pos}
		p.next()
		return w
	}
	if p.tok != token.IDENT {
		p.errorExpected(p.pos, "pattern")
		w := &WildcardPattern{UnderscorePos: p.pos}
		if p.tok != token.COLON && p.tok != token.RPAREN && p.tok != token.COMMA &&
			p.tok != token.RBRACE && p.tok != token.EOF {
			p.next() // skip the offending token so parsing can continue
		}
		return w
	}
	var name ast.Expr = p.parseIdent()
	if p.tok == token.PERIOD {
		p.next()
		name = &ast.SelectorExpr{X: name, Sel: p.parseIdent()}
	}
	cp := &ConstructorPattern{Name: name}
	if p.tok == token.LPAREN {
		cp.Lparen = p.pos
		p.next()
		for p.tok != token.RPAREN && p.tok != token.EOF {
			cp.Args = append(cp.Args, p.parsePattern())
			if p.tok == token.DEFINE {
				p.error(p.pos, "binder patterns may only appear at the top of a case")
				p.next()
				cp.Args = cp.Args[:0]
				continue
			}
			if p.tok != token.COMMA {
				break
			}
			p.next()
		}
		cp.Rparen = p.expect(token.RPAREN)
	}
	return cp
}

// ── Pipelines and composition (v0.3.0) ─────────────────────────────────────
//
// `|>` and `>>>` are token SEQUENCES, not new tokens: OR immediately
// followed by GTR, and SHR immediately followed by GTR. Both sequences are
// invalid Go in every expression position (`>` can never begin an operand),
// so claiming them — with strict adjacency, leaving spaced forms as stock
// errors — preserves the superset. They sit below every Go binary operator:
// tokPrec demotes a claimed operator to LowestPrec, so the stock precedence
// ladder returns without consuming it and parseExpr's tail (parseExtOps)
// takes over. `>>>` binds tighter than `|>`; both left-associative.

// gppExtOp reports whether the current token starts a claimed `|>`,
// `>>>`, or `>=>` sequence (adjacency-checked).
func (p *parser) gppExtOp() bool {
	return p.atPipe() || p.atCompose() || p.atKleisli()
}

func (p *parser) atPipe() bool {
	if p.tok != token.OR {
		return false
	}
	next := p.peekNonCommentTok()
	return next.tok == token.GTR && next.pos == p.pos+1
}

func (p *parser) atCompose() bool {
	if p.tok != token.SHR {
		return false
	}
	next := p.peekNonCommentTok()
	return next.tok == token.GTR && next.pos == p.pos+2
}

// atKleisli claims `>=>`: GEQ immediately followed by GTR (v0.4.0).
func (p *parser) atKleisli() bool {
	if p.tok != token.GEQ {
		return false
	}
	next := p.peekNonCommentTok()
	return next.tok == token.GTR && next.pos == p.pos+2
}

// parseExtOps folds a parsed expression through any `>>>` chain and then
// any `|>` chain. Called from parseExpr's tail, so it applies at every
// expression position.
func (p *parser) parseExtOps(x ast.Expr) ast.Expr {
	x = p.parseComposeChain(x)
	if !p.atPipe() {
		return x
	}
	pipe := &PipeExpr{Head: x}
	p.ext.Pipes = append(p.ext.Pipes, pipe) // creation order; see Extensions doc
	for p.atPipe() {
		opPos := p.pos
		p.next() // consume OR
		p.next() // consume GTR (adjacent: no comment can intervene)
		stage := p.parsePipeStage()
		stage.OpPos = opPos
		pipe.Stages = append(pipe.Stages, stage)
	}
	last := pipe.Stages[len(pipe.Stages)-1]
	pipe.Bad = &ast.BadExpr{From: x.Pos(), To: last.Expr.End()}
	p.markExtBad(pipe.Bad)
	return pipe.Bad
}

// parseComposeChain folds x through a `>>>` / `>=>` chain, if present.
// The two operators share one flattened chain with per-link kinds.
func (p *parser) parseComposeChain(x ast.Expr) ast.Expr {
	if !p.atCompose() && !p.atKleisli() {
		return x
	}
	comp := &ComposeExpr{Fns: []ast.Expr{x}}
	p.ext.Composes = append(p.ext.Composes, comp)
	for p.atCompose() || p.atKleisli() {
		kind := ComposeFn
		if p.atKleisli() {
			kind = ComposeKleisli
		}
		comp.OpPos = append(comp.OpPos, p.pos)
		comp.Ops = append(comp.Ops, kind)
		p.next() // consume SHR or GEQ
		p.next() // consume GTR
		// Stops before the next claimed operator (tokPrec demotion), which
		// yields left associativity and compose binding tighter than `|>`.
		op := p.parseBinaryExpr(nil, token.LowestPrec+1)
		comp.Fns = append(comp.Fns, op)
	}
	comp.Bad = &ast.BadExpr{From: comp.Fns[0].Pos(), To: comp.Fns[len(comp.Fns)-1].End()}
	p.markExtBad(comp.Bad)
	return comp.Bad
}

// parsePipeStage parses one segment after `|>`: a dot-segment
// (`.Name…`, with arbitrary selector/call/index suffixes) or an ordinary
// expression (compose chains fold in; pipelines do not — that keeps `|>`
// left-associative).
func (p *parser) parsePipeStage() *PipeStage {
	stage := &PipeStage{}
	if p.tok == token.PERIOD {
		stage.Dot = p.pos
		p.next()
		if p.tok != token.IDENT {
			p.errorExpected(p.pos, "method or field name")
			stage.Expr = &ast.BadExpr{From: stage.Dot, To: p.pos}
			return stage
		}
		var x ast.Expr = p.parseIdent()
		stage.Expr = p.parsePrimaryExpr(x)
		return stage
	}
	stage.Expr = p.parseComposeChain(p.parseBinaryExpr(nil, token.LowestPrec+1))
	return stage
}

// ── Typed failure (v0.4.0): postfix `?` and expression conditionals ───────

// markExtBad records an extension placeholder so the composite-literal
// suffix guard never treats it as a literal type.
func (p *parser) markExtBad(bad *ast.BadExpr) {
	if p.extBad == nil {
		p.extBad = map[*ast.BadExpr]bool{}
	}
	p.extBad[bad] = true
}

// parseTrySuffix claims an adjacent postfix `?` on x. The caller verified
// p.tok == token.ILLEGAL && p.lit == "?" && p.pos == x.End().
func (p *parser) parseTrySuffix(x ast.Expr) ast.Expr {
	t := &TryExpr{X: x, QPos: p.pos}
	p.claimedQ = append(p.claimedQ, p.pos)
	p.ext.Tries = append(p.ext.Tries, t)
	p.next() // consume the ILLEGAL '?'
	t.Bad = &ast.BadExpr{From: x.Pos(), To: t.QPos + 1}
	p.markExtBad(t.Bad)
	return t.Bad
}

// illegalQuestion is the scanner's exact message for '?'.
var illegalQuestion = fmt.Sprintf("illegal character %#U", '?')

// filterClaimedIllegals drops the scanner's illegal-character error for
// exactly the claimed '?' positions. Matching is by byte offset AND exact
// message, so no other error — including an unclaimed '?' elsewhere —
// can be swallowed.
func (p *parser) filterClaimedIllegals() {
	if len(p.claimedQ) == 0 {
		return
	}
	claimed := make(map[int]bool, len(p.claimedQ))
	for _, pos := range p.claimedQ {
		claimed[p.file.Offset(pos)] = true
	}
	kept := p.errors[:0]
	for _, e := range p.errors {
		if e.Msg == illegalQuestion && claimed[e.Pos.Offset] {
			continue
		}
		kept = append(kept, e)
	}
	p.errors = kept
}

// parseExprFormOperand claims expression-position if/switch/match. It
// returns nil when the current token is not an expression-form claim.
func (p *parser) parseExprFormOperand() ast.Expr {
	switch {
	case p.tok == token.IF:
		root := p.parseIfExpr()
		root.Bad = &ast.BadExpr{From: root.If, To: ifExprEnd(root)}
		p.markExtBad(root.Bad)
		p.ext.IfExprs = append(p.ext.IfExprs, root)
		return root.Bad
	case p.tok == token.SWITCH:
		se := p.parseSwitchExpr()
		se.Bad = &ast.BadExpr{From: se.Switch, To: se.Rbrace + 1}
		p.markExtBad(se.Bad)
		p.ext.SwitchExprs = append(p.ext.SwitchExprs, se)
		return se.Bad
	case p.tok == token.IDENT && p.lit == "match" && exprMatchClaims(p.peekNonComment()):
		me := p.parseMatchExpr()
		me.Bad = &ast.BadExpr{From: me.Match, To: me.Rbrace + 1}
		p.markExtBad(me.Bad)
		p.ext.MatchExprs = append(p.ext.MatchExprs, me)
		return me.Bad
	}
	return nil
}

// exprMatchClaims is the expression-position claim table for contextual
// `match` — STRICTER than the statement table: binary-operator tokens
// (+ - * & ^) validly continue a Go expression whose operand is the
// identifier `match`, so they are not claimable here. Neither is `<-`:
// statement sends (`match <- ch`, valid Go) parse through this same
// expression path, so a receive subject must be parenthesized.
func exprMatchClaims(tok token.Token) bool {
	switch tok {
	case token.IDENT, token.INT, token.FLOAT, token.IMAG, token.CHAR, token.STRING,
		token.FUNC, token.STRUCT, token.MAP, token.CHAN, token.INTERFACE,
		token.NOT:
		return true
	}
	return false
}

func ifExprEnd(root *IfExpr) token.Pos {
	for root.ElseIf != nil {
		root = root.ElseIf
	}
	return root.ElseRbrace + 1
}

// parseIfExpr parses `if cond { e } else …` (the `if` token is current).
func (p *parser) parseIfExpr() *IfExpr {
	e := &IfExpr{If: p.pos}
	p.next() // consume `if`
	prevLev := p.exprLev
	p.exprLev = -1
	e.Cond = p.parseRhs()
	p.exprLev = prevLev
	if p.tok == token.DEFINE || p.tok == token.ASSIGN || p.tok == token.SEMICOLON {
		p.error(p.pos, "if expressions cannot declare variables; bind before the if")
	}
	e.Lbrace = p.expect(token.LBRACE)
	e.Then = p.parseBracedExprBody()
	e.Rbrace = p.expect(token.RBRACE)

	if p.tok == token.SEMICOLON && p.lit == "\n" && p.peekNonComment() == token.ELSE {
		p.error(p.pos, "unexpected newline before else (write '} else')")
		p.next()
	}
	if p.tok != token.ELSE {
		p.error(p.pos, "missing else in if expression (every if expression requires an else)")
		return e
	}
	e.ElsePos = p.pos
	p.next() // consume `else`
	if p.tok == token.IF {
		e.ElseIf = p.parseIfExpr()
		return e
	}
	e.ElseLbrace = p.expect(token.LBRACE)
	e.Else = p.parseBracedExprBody()
	e.ElseRbrace = p.expect(token.RBRACE)
	return e
}

// parseBracedExprBody parses the single expression inside an arm/branch
// brace pair, tolerating the ASI semicolon before `}`.
func (p *parser) parseBracedExprBody() ast.Expr {
	prevLev := p.exprLev
	if p.exprLev < 0 {
		p.exprLev = 0
	}
	x := p.parseExpr()
	p.exprLev = prevLev
	if p.tok == token.SEMICOLON {
		p.next()
	}
	return x
}

// parseSwitchExpr parses `switch [tag] { arms }` (the `switch` token is
// current).
func (p *parser) parseSwitchExpr() *SwitchExpr {
	e := &SwitchExpr{Switch: p.pos}
	p.next()
	if p.tok != token.LBRACE {
		prevLev := p.exprLev
		p.exprLev = -1
		e.Tag = p.parseRhs()
		p.exprLev = prevLev
		if p.tok == token.SEMICOLON {
			p.error(p.pos, "switch expressions cannot have an init statement")
			p.next()
		}
	}
	e.Lbrace = p.expect(token.LBRACE)
	for p.tok == token.CASE || p.tok == token.DEFAULT {
		e.Arms = append(e.Arms, p.parseSwitchExprArm())
	}
	e.Rbrace = p.expect(token.RBRACE)
	return e
}

func (p *parser) parseSwitchExprArm() *SwitchExprArm {
	arm := &SwitchExprArm{Case: p.pos}
	if p.tok == token.CASE {
		p.next()
		prevLev := p.exprLev
		if p.exprLev < 0 {
			p.exprLev = 0
		}
		arm.Values = append(arm.Values, p.parseRhs())
		for p.tok == token.COMMA {
			p.next()
			arm.Values = append(arm.Values, p.parseRhs())
		}
		p.exprLev = prevLev
	} else {
		p.next() // consume `default`
	}
	arm.Colon = p.expect(token.COLON)
	arm.Value = p.parseArmValue()
	return arm
}

// parseArmValue parses one arm expression, tolerating the trailing ASI
// semicolon.
func (p *parser) parseArmValue() ast.Expr {
	prevLev := p.exprLev
	if p.exprLev < 0 {
		p.exprLev = 0
	}
	x := p.parseExpr()
	p.exprLev = prevLev
	if p.tok == token.SEMICOLON {
		p.next()
	}
	return x
}

// parseMatchExpr parses `match subject { case pattern: expr … }` (the
// contextual `match` identifier is current).
func (p *parser) parseMatchExpr() *MatchExpr {
	e := &MatchExpr{Match: p.pos}
	p.next() // consume `match`
	prevLev := p.exprLev
	p.exprLev = -1
	e.Subject = p.parseRhs()
	p.exprLev = prevLev
	e.Lbrace = p.expect(token.LBRACE)
	for p.tok == token.CASE || p.tok == token.DEFAULT {
		e.Arms = append(e.Arms, p.parseMatchExprArm())
	}
	e.Rbrace = p.expect(token.RBRACE)
	return e
}

func (p *parser) parseMatchExprArm() *MatchExprArm {
	arm := &MatchExprArm{Case: p.pos}
	if p.tok == token.DEFAULT {
		p.error(p.pos, "match expressions do not have a default case; use 'case _:'")
		p.next()
		arm.Pattern = &WildcardPattern{UnderscorePos: arm.Case}
		arm.Colon = p.expect(token.COLON)
		arm.Value = p.parseArmValue()
		return arm
	}
	p.expect(token.CASE)
	if p.tok == token.IDENT && p.peekNonComment() == token.DEFINE {
		if p.lit == "_" {
			p.error(p.pos, "cannot bind to _; name the binder or drop it")
		}
		arm.Binder = p.parseIdent()
		arm.Define = p.pos
		p.next() // consume :=
		if p.tok == token.IDENT && p.lit == "_" {
			p.error(p.pos, "cannot bind a wildcard pattern")
		}
	}
	arm.Pattern = p.parsePattern()
	arm.Colon = p.expect(token.COLON)
	arm.Value = p.parseArmValue()
	return arm
}

// ── Entry point ────────────────────────────────────────────────────────────

// parseFileExt mirrors ParseFile but also returns the file's G++
// extension constructs.
func parseFileExt(fset *token.FileSet, filename string, src any, mode Mode) (f *ast.File, ext *Extensions, err error) {
	if fset == nil {
		panic("parser.ParseFileExt: no token.FileSet provided (fset == nil)")
	}
	text, err := readSource(filename, src)
	if err != nil {
		return nil, nil, err
	}
	file := fset.AddFile(filename, -1, len(text))

	var p parser
	defer func() {
		if e := recover(); e != nil {
			bail, ok := e.(bailout)
			if !ok {
				panic(e)
			} else if bail.msg != "" {
				p.errors.Add(p.file.Position(bail.pos), bail.msg)
			}
		}
		if f == nil {
			f = &ast.File{
				Name:  new(ast.Ident),
				Scope: ast.NewScope(nil),
			}
		}
		f.FileStart = token.Pos(file.Base())
		f.FileEnd = file.End()
		ext = &p.ext
		p.filterClaimedIllegals()
		p.errors.Sort()
		err = p.errors.Err()
	}()

	p.init(file, text, mode)
	f = p.parseFile()
	return
}
