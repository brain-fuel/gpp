// G++ grammar hooks. This file is gpp's own (not vendored). The vendored
// parser calls into it from five marked hunks; everything else lives here.
package parser

import (
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
// `enum { … }` form via the contextual keyword.
func (p *parser) parseTypeSpecType(spec *ast.TypeSpec) {
	if p.tok == token.IDENT && p.lit == "enum" && p.peekNonComment() == token.LBRACE {
		p.parseEnumType(spec)
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

// gppExtOp reports whether the current token starts a claimed `|>` or
// `>>>` sequence (adjacency-checked).
func (p *parser) gppExtOp() bool {
	return p.atPipe() || p.atCompose()
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
	return pipe.Bad
}

// parseComposeChain folds x through a `>>>` chain, if present.
func (p *parser) parseComposeChain(x ast.Expr) ast.Expr {
	if !p.atCompose() {
		return x
	}
	comp := &ComposeExpr{Fns: []ast.Expr{x}}
	p.ext.Composes = append(p.ext.Composes, comp)
	for p.atCompose() {
		comp.OpPos = append(comp.OpPos, p.pos)
		p.next() // consume SHR
		p.next() // consume GTR
		// Stops before the next claimed operator (tokPrec demotion), which
		// yields left associativity and `>>>` binding tighter than `|>`.
		op := p.parseBinaryExpr(nil, token.LowestPrec+1)
		comp.Fns = append(comp.Fns, op)
	}
	comp.Bad = &ast.BadExpr{From: comp.Fns[0].Pos(), To: comp.Fns[len(comp.Fns)-1].End()}
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
		p.errors.Sort()
		err = p.errors.Err()
	}()

	p.init(file, text, mode)
	f = p.parseFile()
	return
}
