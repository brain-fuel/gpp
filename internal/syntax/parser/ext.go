// G++ extension nodes and entry points. This file is gpp's own (not
// vendored from GOROOT): the fork parses G++'s two grammar extensions —
// enum declarations and match statements — into the side-table types below,
// leaving stock placeholder nodes (*ast.BadExpr / *ast.BadStmt) in the
// *ast.File so every downstream go/ast consumer keeps working.
package parser

import (
	"go/ast"
	"go/token"
)

// EnumDecl is one `type Name [TypeParams] enum { … }` declaration.
type EnumDecl struct {
	Gen     *ast.GenDecl  // enclosing declaration; filled by syntax.ParseFile
	Spec    *ast.TypeSpec // Name/TypeParams are real; Spec.Type is an *ast.BadExpr spanning the enum body
	EnumPos token.Pos     // position of the `enum` keyword
	Lbrace  token.Pos
	Variants []*Variant
	Rbrace  token.Pos
}

// Variant is one constructor declaration inside an enum body.
type Variant struct {
	Doc          *ast.CommentGroup
	Name         *ast.Ident
	Params       *ast.FieldList // nil for a bare variant (Point); (…) may be empty
	Result       ast.Expr       // GADT result type; nil ⇒ enum applied to its own type parameters
	Comment      *ast.CommentGroup
	NameOverride string // //gpp:name from Doc; filled by syntax.ParseFile
}

// MatchStmt is one `match subject { case … }` statement.
type MatchStmt struct {
	Stmt    *ast.BadStmt // placeholder occupying this match's slot in the enclosing block
	Match   token.Pos    // position of the `match` keyword
	Subject ast.Expr
	Lbrace  token.Pos
	Cases   []*CaseClause
	Rbrace  token.Pos
}

// CaseClause is one `case [binder :=] pattern:` arm.
type CaseClause struct {
	Case    token.Pos
	Binder  *ast.Ident // c in `case c := Circle(r):`; nil if absent
	Define  token.Pos  // position of ":="; NoPos if absent
	Pattern Pattern    // WildcardPattern for `case _:`
	Colon   token.Pos
	Body    []ast.Stmt // stock statements; nested matches appear as *ast.BadStmt
}

// Pattern is a match pattern: wildcard or (possibly nested) constructor.
type Pattern interface {
	Pos() token.Pos
	End() token.Pos
	pattern()
}

// WildcardPattern is `_`.
type WildcardPattern struct{ UnderscorePos token.Pos }

func (p *WildcardPattern) Pos() token.Pos { return p.UnderscorePos }
func (p *WildcardPattern) End() token.Pos { return p.UnderscorePos + 1 }
func (p *WildcardPattern) pattern()       {}

// ConstructorPattern is `Name(args…)` or a bare `Name`. With Lparen ==
// token.NoPos it is a bare name: a nullary constructor or a field binder —
// the parser does not decide; resolution does (a constructor name shadows
// binding).
type ConstructorPattern struct {
	Name   ast.Expr // *ast.Ident or *ast.SelectorExpr (qualified)
	Lparen token.Pos
	Args   []Pattern
	Rparen token.Pos
}

func (p *ConstructorPattern) Pos() token.Pos { return p.Name.Pos() }
func (p *ConstructorPattern) End() token.Pos {
	if p.Rparen.IsValid() {
		return p.Rparen + 1
	}
	return p.Name.End()
}
func (p *ConstructorPattern) pattern() {}

// PipeExpr is one `head |> stage |> stage` pipeline expression (v0.3.0).
type PipeExpr struct {
	Bad    *ast.BadExpr // placeholder occupying the pipeline's span
	Head   ast.Expr     // real expression; may itself be a *ast.BadExpr
	Stages []*PipeStage // one per |>, source order; len >= 1
}

// PipeStage is one `|> segment`.
type PipeStage struct {
	OpPos token.Pos // position of `|` in `|>`
	Dot   token.Pos // position of `.` for a dot-segment; NoPos otherwise
	// Expr is a stock expression. Dot-segment: rooted at the post-dot
	// name, with arbitrary selector/call/index suffixes (`.A().B(c)`).
	// Plain segment: any expression; nested pipes/composes appear as
	// *ast.BadExpr resolvable via the File lookup maps.
	Expr ast.Expr
}

// ComposeExpr is one `f >>> g >>> h` chain (left-associative, flattened).
type ComposeExpr struct {
	Bad   *ast.BadExpr
	Fns   []ast.Expr  // len >= 2; operands may be *ast.BadExpr
	OpPos []token.Pos // position of `>>` in each `>>>`; len == len(Fns)-1
}

// Extensions collects a file's G++ constructs.
//
// Pipes and Composes are in CREATION order: a node registers when its
// first operator token is claimed, so extensions nested in stages/right
// operands follow their encloser, while extensions nested in the
// head/left operand precede it. Downstream phases must resolve
// placeholders by pointer (File.PipeFor / File.ComposeFor), never by
// slice position.
type Extensions struct {
	Enums    []*EnumDecl
	Matches  []*MatchStmt // pre-order; includes matches nested inside arms
	Pipes    []*PipeExpr
	Composes []*ComposeExpr
}

// ParseFileExt parses G++ source: stock Go grammar plus enum declarations,
// match statements, and type parameters on methods.
func ParseFileExt(fset *token.FileSet, filename string, src []byte, mode Mode) (*ast.File, *Extensions, error) {
	f, ext, err := parseFileExt(fset, filename, src, mode)
	return f, ext, err
}
