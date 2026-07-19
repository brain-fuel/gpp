// Package syntax parses .gpp source: Go grammar plus G++'s extensions —
// type parameters on methods (v0.1.0), enum declarations and match
// statements (v0.2.0). It fronts a vendored fork of go/parser (see
// internal/syntax/parser); the *ast.File it produces is fully stock, with
// extension constructs occupying their source spans as placeholder nodes
// and the real structure exposed via Methods, Enums, and Matches.
package syntax

import (
	"fmt"
	"go/ast"
	"go/token"

	"goforge.dev/gpp/internal/syntax/parser"
)

// Re-exported extension node types; see internal/syntax/parser/ext.go.
type (
	EnumDecl           = parser.EnumDecl
	ClassDecl          = parser.ClassDecl
	ClassMember        = parser.ClassMember
	InstanceDecl       = parser.InstanceDecl
	InstanceMember     = parser.InstanceMember
	DelegateField      = parser.DelegateField
	QuantityParam      = parser.QuantityParam
	TotalFunc          = parser.TotalFunc
	Variant            = parser.Variant
	MatchStmt          = parser.MatchStmt
	CaseClause         = parser.CaseClause
	Pattern            = parser.Pattern
	WildcardPattern    = parser.WildcardPattern
	ConstructorPattern = parser.ConstructorPattern
	PipeExpr           = parser.PipeExpr
	PipeStage          = parser.PipeStage
	ComposeExpr        = parser.ComposeExpr
	ComposeKind        = parser.ComposeKind
	TryExpr            = parser.TryExpr
	IfExpr             = parser.IfExpr
	SwitchExpr         = parser.SwitchExpr
	SwitchExprArm      = parser.SwitchExprArm
	MatchExpr          = parser.MatchExpr
	MatchExprArm       = parser.MatchExprArm
)

// Composition operator kinds.
const (
	ComposeFn      = parser.ComposeFn
	ComposeKleisli = parser.ComposeKleisli
)

// File is one parsed .gpp file.
type File struct {
	Path    string
	Src     []byte
	Fset    *token.FileSet
	TokFile *token.File
	AST     *ast.File // stock AST; enum bodies are BadExpr, matches BadStmt
	Methods []*GenericMethod
	Enums   []*EnumDecl  // source order
	Classes   []*ClassDecl    // source order (v0.5.0)
	Instances []*InstanceDecl // source order (v0.5.0)
	Delegates []*DelegateField // source order (v0.6.0)

	Quantities []*QuantityParam // source order (v0.7.0)
	Totals     []*TotalFunc     // source order (v0.7.0)
	Matches []*MatchStmt // pre-order (nested matches follow their parent)

	// Pipes and Composes are in creation order (extensions nested in a
	// head/left operand precede their encloser); resolve placeholders by
	// pointer via PipeFor/ComposeFor, never by slice position.
	Pipes    []*PipeExpr
	Composes []*ComposeExpr

	// v0.4.0 typed-failure constructs, creation order.
	Tries       []*TryExpr
	IfExprs     []*IfExpr
	SwitchExprs []*SwitchExpr
	MatchExprs  []*MatchExpr

	matchOf     map[*ast.BadStmt]*MatchStmt
	pipeOf      map[*ast.BadExpr]*PipeExpr
	composeOf   map[*ast.BadExpr]*ComposeExpr
	tryOf       map[*ast.BadExpr]*TryExpr
	ifOf        map[*ast.BadExpr]*IfExpr
	switchExpOf map[*ast.BadExpr]*SwitchExpr
	matchExpOf  map[*ast.BadExpr]*MatchExpr
}

// GenericMethod is a method declaration carrying its own type parameters.
type GenericMethod struct {
	Decl *ast.FuncDecl // TypeParams present natively (fork keeps them)

	RecvName     string   // receiver identifier as written; "" if absent
	RecvTypeName string   // base named type, e.g. "Stack"
	RecvPointer  bool     // *Stack[T] receiver
	RecvTParams  []string // receiver type parameter names, e.g. ["T"]

	// LBrack and RBrack are byte offsets in Src of the method's type
	// parameter brackets.
	LBrack, RBrack int

}

// Offset converts a token.Pos within f to a byte offset in f.Src.
func (f *File) Offset(pos token.Pos) int { return f.TokFile.Offset(pos) }

// MatchFor resolves a placeholder statement to its match statement.
func (f *File) MatchFor(bad *ast.BadStmt) (*MatchStmt, bool) {
	m, ok := f.matchOf[bad]
	return m, ok
}

// PipeFor resolves a placeholder expression to its pipeline.
func (f *File) PipeFor(bad *ast.BadExpr) (*PipeExpr, bool) {
	p, ok := f.pipeOf[bad]
	return p, ok
}

// ComposeFor resolves a placeholder expression to its composition.
func (f *File) ComposeFor(bad *ast.BadExpr) (*ComposeExpr, bool) {
	c, ok := f.composeOf[bad]
	return c, ok
}

// TryFor resolves a placeholder expression to its try suffix.
func (f *File) TryFor(bad *ast.BadExpr) (*TryExpr, bool) {
	t, ok := f.tryOf[bad]
	return t, ok
}

// IfFor resolves a placeholder expression to its if expression.
func (f *File) IfFor(bad *ast.BadExpr) (*IfExpr, bool) {
	e, ok := f.ifOf[bad]
	return e, ok
}

// SwitchExprFor resolves a placeholder expression to its switch expression.
func (f *File) SwitchExprFor(bad *ast.BadExpr) (*SwitchExpr, bool) {
	e, ok := f.switchExpOf[bad]
	return e, ok
}

// MatchExprFor resolves a placeholder expression to its match expression.
func (f *File) MatchExprFor(bad *ast.BadExpr) (*MatchExpr, bool) {
	e, ok := f.matchExpOf[bad]
	return e, ok
}

// flowSpan returns the byte span of a flow extension's placeholder.
func (f *File) flowSpan(bad *ast.BadExpr) (int, int) {
	return f.Offset(bad.From), f.Offset(bad.To)
}

// extPlaceholders lists every expression-extension placeholder.
func (f *File) extPlaceholders() []*ast.BadExpr {
	var out []*ast.BadExpr
	for _, p := range f.Pipes {
		out = append(out, p.Bad)
	}
	for _, c := range f.Composes {
		out = append(out, c.Bad)
	}
	for _, t := range f.Tries {
		out = append(out, t.Bad)
	}
	for _, e := range f.IfExprs {
		out = append(out, e.Bad)
	}
	for _, e := range f.SwitchExprs {
		out = append(out, e.Bad)
	}
	for _, e := range f.MatchExprs {
		out = append(out, e.Bad)
	}
	return out
}

// OutermostExt lists the expression-extension placeholders whose spans are
// not contained inside another extension expression's span — the set
// pass-1 lowering rewrites (nested extensions render recursively inside
// them). Ordered by source position.
func (f *File) OutermostExt() []*ast.BadExpr {
	all := f.extPlaceholders()
	type span struct{ from, to int }
	spans := make([]span, len(all))
	for i, b := range all {
		spans[i] = span{f.Offset(b.From), f.Offset(b.To)}
	}
	contained := func(i int) bool {
		for j, s := range spans {
			if j == i {
				continue
			}
			if s.from <= spans[i].from && spans[i].to <= s.to && !(s.from == spans[i].from && s.to == spans[i].to) {
				return true
			}
		}
		return false
	}
	var out []*ast.BadExpr
	for i, b := range all {
		if !contained(i) {
			out = append(out, b)
		}
	}
	sortBadBySpan(f, out)
	return out
}

func sortBadBySpan(f *File, bs []*ast.BadExpr) {
	for i := 1; i < len(bs); i++ {
		for j := i; j > 0 && f.Offset(bs[j].From) < f.Offset(bs[j-1].From); j-- {
			bs[j], bs[j-1] = bs[j-1], bs[j]
		}
	}
}

// OutermostFlow lists the pipelines and compositions whose spans are not
// contained inside another flow extension's span — the ones pass-1
// lowering must rewrite (nested flows render recursively inside them).
func (f *File) OutermostFlow() (pipes []*PipeExpr, composes []*ComposeExpr) {
	type span struct{ from, to int }
	var all []span
	for _, p := range f.Pipes {
		from, to := f.flowSpan(p.Bad)
		all = append(all, span{from, to})
	}
	for _, c := range f.Composes {
		from, to := f.flowSpan(c.Bad)
		all = append(all, span{from, to})
	}
	contained := func(from, to int) bool {
		for _, s := range all {
			if s.from <= from && to <= s.to && !(s.from == from && s.to == to) {
				return true
			}
		}
		return false
	}
	for _, p := range f.Pipes {
		if from, to := f.flowSpan(p.Bad); !contained(from, to) {
			pipes = append(pipes, p)
		}
	}
	for _, c := range f.Composes {
		if from, to := f.flowSpan(c.Bad); !contained(from, to) {
			composes = append(composes, c)
		}
	}
	return pipes, composes
}

// ParseFile parses .gpp source. Genuine syntax errors are returned as a
// scanner.ErrorList.
func ParseFile(fset *token.FileSet, path string, src []byte) (*File, error) {
	astFile, ext, err := parser.ParseFileExt(fset, path, src, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		return nil, err
	}
	f := &File{
		Path:      path,
		Src:       src,
		Fset:      fset,
		TokFile:   fset.File(astFile.Pos()),
		AST:       astFile,
		Enums:     ext.Enums,
		Classes:   ext.Classes,
		Instances: ext.Instances,
		Delegates: ext.Delegates,
		Quantities: ext.Quantities,
		Totals:     ext.Totals,
		Matches:   ext.Matches,
		Pipes:       ext.Pipes,
		Composes:    ext.Composes,
		Tries:       ext.Tries,
		IfExprs:     ext.IfExprs,
		SwitchExprs: ext.SwitchExprs,
		MatchExprs:  ext.MatchExprs,
		matchOf:     map[*ast.BadStmt]*MatchStmt{},
		pipeOf:      map[*ast.BadExpr]*PipeExpr{},
		composeOf:   map[*ast.BadExpr]*ComposeExpr{},
		tryOf:       map[*ast.BadExpr]*TryExpr{},
		ifOf:        map[*ast.BadExpr]*IfExpr{},
		switchExpOf: map[*ast.BadExpr]*SwitchExpr{},
		matchExpOf:  map[*ast.BadExpr]*MatchExpr{},
	}
	for _, m := range ext.Matches {
		f.matchOf[m.Stmt] = m
	}
	for _, p := range ext.Pipes {
		f.pipeOf[p.Bad] = p
	}
	for _, c := range ext.Composes {
		f.composeOf[c.Bad] = c
	}
	for _, t := range ext.Tries {
		f.tryOf[t.Bad] = t
	}
	for _, e := range ext.IfExprs {
		f.ifOf[e.Bad] = e
	}
	for _, e := range ext.SwitchExprs {
		f.switchExpOf[e.Bad] = e
	}
	for _, e := range ext.MatchExprs {
		f.matchExpOf[e.Bad] = e
	}
	// Enclosing GenDecl for each enum (doc comments of ungrouped decls
	// live on the GenDecl, not the TypeSpec).
	specToGen := map[*ast.TypeSpec]*ast.GenDecl{}
	for _, decl := range astFile.Decls {
		if gd, ok := decl.(*ast.GenDecl); ok {
			for _, spec := range gd.Specs {
				if ts, ok := spec.(*ast.TypeSpec); ok {
					specToGen[ts] = gd
				}
			}
		}
	}
	for _, c := range ext.Classes {
		c.Gen = specToGen[c.Spec]
	}
	for _, e := range ext.Enums {
		e.Gen = specToGen[e.Spec]
	}
	// Generic methods: the fork keeps method type parameters natively.
	for _, decl := range astFile.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Recv == nil || fd.Type.TypeParams == nil {
			continue
		}
		gm := &GenericMethod{
			Decl:   fd,
			LBrack: f.Offset(fd.Type.TypeParams.Opening),
			RBrack: f.Offset(fd.Type.TypeParams.Closing),
		}
		if err := gm.fillReceiver(); err != nil {
			return nil, fmt.Errorf("%s: %w", path, err)
		}
		f.Methods = append(f.Methods, gm)
	}
	return f, nil
}

// NewMethod builds method info for an ordinary (non-generic) method
// declaration, e.g. an enum method that lowers like a generic method with
// zero method type parameters.
func NewMethod(fd *ast.FuncDecl) (*GenericMethod, error) {
	gm := &GenericMethod{Decl: fd, LBrack: -1, RBrack: -1}
	if err := gm.fillReceiver(); err != nil {
		return nil, err
	}
	return gm, nil
}

// fillReceiver extracts receiver shape from the declaration.
func (m *GenericMethod) fillReceiver() error {
	fd := m.Decl
	if len(fd.Recv.List) != 1 {
		return fmt.Errorf("method %s: malformed receiver", fd.Name.Name)
	}
	field := fd.Recv.List[0]
	if len(field.Names) == 1 {
		m.RecvName = field.Names[0].Name
	}
	t := field.Type
	if p, ok := t.(*ast.ParenExpr); ok {
		t = p.X
	}
	if s, ok := t.(*ast.StarExpr); ok {
		m.RecvPointer = true
		t = s.X
	}
	if p, ok := t.(*ast.ParenExpr); ok {
		t = p.X
	}
	switch bt := t.(type) {
	case *ast.Ident:
		m.RecvTypeName = bt.Name
	case *ast.IndexExpr:
		id, ok := bt.X.(*ast.Ident)
		if !ok {
			return fmt.Errorf("method %s: unsupported receiver type", fd.Name.Name)
		}
		m.RecvTypeName = id.Name
		tp, ok := bt.Index.(*ast.Ident)
		if !ok {
			return fmt.Errorf("method %s: receiver type parameter must be an identifier", fd.Name.Name)
		}
		m.RecvTParams = []string{tp.Name}
	case *ast.IndexListExpr:
		id, ok := bt.X.(*ast.Ident)
		if !ok {
			return fmt.Errorf("method %s: unsupported receiver type", fd.Name.Name)
		}
		m.RecvTypeName = id.Name
		for _, idx := range bt.Indices {
			tp, ok := idx.(*ast.Ident)
			if !ok {
				return fmt.Errorf("method %s: receiver type parameter must be an identifier", fd.Name.Name)
			}
			m.RecvTParams = append(m.RecvTParams, tp.Name)
		}
	default:
		return fmt.Errorf("method %s: unsupported receiver type", fd.Name.Name)
	}
	return nil
}
