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
	Doc     *ast.CommentGroup
	Name    *ast.Ident
	TParams *ast.FieldList // bounded existential type parameters (v0.6.0); nil otherwise
	Params  *ast.FieldList // nil for a bare variant (Point); (…) may be empty
	Result  ast.Expr       // GADT result type; nil ⇒ enum applied to its own type parameters
	Comment *ast.CommentGroup
}

// DelegateField is one struct field marked with the trailing `delegate`
// contextual keyword (v0.6.0): the outer type gains generated forwarders
// for the field's interface methods.
type DelegateField struct {
	Field       *ast.Field
	DelegatePos token.Pos
}

// QuantityParam is one parameter carrying a QTT quantity prefix
// (v0.7.0): `0 n int` (erased), `1 f *os.File` (linear), or `m x T`
// where m names a multiplicity type parameter. The prefix spans
// [QPos, Name.Pos) in the source and is stripped by lowering.
type QuantityParam struct {
	Quantity string     // "0", "1", or a multiplicity variable name
	QPos     token.Pos  // start of the quantity token
	Name     *ast.Ident // the parameter name the quantity annotates
}

// TotalFunc is one `total func` declaration (v0.7.0): the function is
// checked for structural termination and becomes callable in types.
type TotalFunc struct {
	Decl     *ast.FuncDecl
	TotalPos token.Pos // position of the `total` keyword
}

// ClassDecl is one `type Name[T any] class { … }` declaration (v0.5.0).
type ClassDecl struct {
	Gen      *ast.GenDecl  // enclosing declaration; filled by syntax.ParseFile
	Spec     *ast.TypeSpec // Name/TypeParams are real; Spec.Type is an *ast.BadExpr spanning the class body
	ClassPos token.Pos     // position of the `class` keyword
	Lbrace   token.Pos
	Members  []*ClassMember
	Rbrace   token.Pos
}

// ClassMember is one embed, operation, or law inside a class body.
// Exactly one of Embed / Name is set: embeds carry only Embed; ops and
// laws carry Name (+ Params, and for ops an optional Result and optional
// default Body; laws always have a Body and an implicit bool result).
type ClassMember struct {
	Doc     *ast.CommentGroup
	LawPos  token.Pos      // position of `law`; NoPos for ops and embeds
	Embed   ast.Expr       // Semigroup[T] / pkg.Semigroup[T]; nil for ops/laws
	Name    *ast.Ident     // op or law name; nil for embeds
	Params  *ast.FieldList // ops/laws; nil for embeds
	Result  ast.Expr       // op result type; nil for void ops and laws
	Body    *ast.BlockStmt // law: required; op: optional default; embed: nil
	Comment *ast.CommentGroup
}

// InstanceDecl is one top-level `instance Name [TParams] Class[Args] { … }`
// declaration (v0.5.0).
type InstanceDecl struct {
	Decl        *ast.BadDecl // placeholder occupying this instance's slot in File.Decls
	Doc         *ast.CommentGroup
	InstancePos token.Pos
	Name        *ast.Ident
	TParams     *ast.FieldList // generic instances (SliceConcat[T any]); nil otherwise
	Class       ast.Expr       // IndexExpr/IndexListExpr over Ident or SelectorExpr
	Lbrace      token.Pos
	Members     []*InstanceMember
	Rbrace      token.Pos
}

// InstanceMember is one operation implementation inside an instance body.
type InstanceMember struct {
	Doc     *ast.CommentGroup
	Name    *ast.Ident
	Params  *ast.FieldList
	Result  ast.Expr       // nil for void ops
	Body    *ast.BlockStmt // required
	Comment *ast.CommentGroup
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
	Alts    []Pattern  // additional alternatives of a multi-pattern arm (v0.12.0); nil otherwise
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

// ComposeKind discriminates the operator of one composition link.
type ComposeKind int

const (
	ComposeFn      ComposeKind = iota // >>> — one-track composition
	ComposeKleisli                    // >=> — railway (Kleisli) composition
)

// ComposeExpr is one `f >>> g >=> h` chain (left-associative, flattened;
// the two operators share a precedence level and mix freely).
type ComposeExpr struct {
	Bad   *ast.BadExpr
	Fns   []ast.Expr    // len >= 2; operands may be *ast.BadExpr
	OpPos []token.Pos   // first char of each operator; len == len(Fns)-1
	Ops   []ComposeKind // operator of each link; len == len(Fns)-1
}

// TryExpr is one postfix `expr?` failure-propagation suffix (v0.4.0).
type TryExpr struct {
	Bad  *ast.BadExpr // placeholder spanning X.Pos()..QPos+1
	X    ast.Expr     // the fallible expression; may itself be a placeholder
	QPos token.Pos    // position of '?'
}

// IfExpr is one `if cond { e } else …` expression (v0.4.0). Only the root
// of an else-if chain carries Bad and registers in Extensions.IfExprs;
// else-if links hang off ElseIf with Bad == nil.
type IfExpr struct {
	Bad        *ast.BadExpr // nil on else-if links
	If         token.Pos
	Cond       ast.Expr
	Lbrace     token.Pos
	Then       ast.Expr
	Rbrace     token.Pos
	ElsePos    token.Pos
	ElseIf     *IfExpr   // `else if …`; nil if braced else
	ElseLbrace token.Pos // braced else only
	Else       ast.Expr  // braced else only; nil when ElseIf != nil
	ElseRbrace token.Pos
}

// SwitchExpr is one `switch [tag] { case …: e … }` expression (v0.4.0).
type SwitchExpr struct {
	Bad    *ast.BadExpr
	Switch token.Pos
	Tag    ast.Expr // nil for a tag-less switch
	Lbrace token.Pos
	Arms   []*SwitchExprArm
	Rbrace token.Pos
}

// SwitchExprArm is one `case v1, v2: expr` or `default: expr` arm.
type SwitchExprArm struct {
	Case   token.Pos  // position of `case` or `default`
	Values []ast.Expr // nil ⇒ default arm
	Colon  token.Pos
	Value  ast.Expr
}

// MatchExpr is one `match subject { case pattern: expr … }` expression.
type MatchExpr struct {
	Bad     *ast.BadExpr
	Match   token.Pos
	Subject ast.Expr
	Lbrace  token.Pos
	Arms    []*MatchExprArm
	Rbrace  token.Pos
}

// MatchExprArm is one `case [binder :=] pattern: expr` arm.
type MatchExprArm struct {
	Case    token.Pos
	Binder  *ast.Ident // nil if absent
	Define  token.Pos  // NoPos if absent
	Pattern Pattern
	Colon   token.Pos
	Value   ast.Expr
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
	// v0.4.0 — creation order; resolve placeholders by pointer.
	Tries       []*TryExpr
	IfExprs     []*IfExpr // roots only; else-if links via ElseIf
	SwitchExprs []*SwitchExpr
	MatchExprs  []*MatchExpr
	// v0.5.0 — source order.
	Classes   []*ClassDecl
	Instances []*InstanceDecl
	// v0.6.0 — source order.
	Delegates []*DelegateField
	// v0.7.0 — source order.
	Quantities []*QuantityParam
	Totals     []*TotalFunc
}

// ParseFileExt parses G++ source: stock Go grammar plus enum declarations,
// match statements, and type parameters on methods.
func ParseFileExt(fset *token.FileSet, filename string, src []byte, mode Mode) (*ast.File, *Extensions, error) {
	f, ext, err := parseFileExt(fset, filename, src, mode)
	return f, ext, err
}
