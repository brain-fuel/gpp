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

	"goforge.dev/gpp/internal/directive"
	"goforge.dev/gpp/internal/syntax/parser"
)

// Re-exported extension node types; see internal/syntax/parser/ext.go.
type (
	EnumDecl           = parser.EnumDecl
	Variant            = parser.Variant
	MatchStmt          = parser.MatchStmt
	CaseClause         = parser.CaseClause
	Pattern            = parser.Pattern
	WildcardPattern    = parser.WildcardPattern
	ConstructorPattern = parser.ConstructorPattern
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
	Matches []*MatchStmt // pre-order (nested matches follow their parent)

	matchOf map[*ast.BadStmt]*MatchStmt
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

	NameOverride string // //gpp:name value, "" if absent
}

// Offset converts a token.Pos within f to a byte offset in f.Src.
func (f *File) Offset(pos token.Pos) int { return f.TokFile.Offset(pos) }

// MatchFor resolves a placeholder statement to its match statement.
func (f *File) MatchFor(bad *ast.BadStmt) (*MatchStmt, bool) {
	m, ok := f.matchOf[bad]
	return m, ok
}

// ParseFile parses .gpp source. Genuine syntax errors are returned as a
// scanner.ErrorList.
func ParseFile(fset *token.FileSet, path string, src []byte) (*File, error) {
	astFile, ext, err := parser.ParseFileExt(fset, path, src, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		return nil, err
	}
	f := &File{
		Path:    path,
		Src:     src,
		Fset:    fset,
		TokFile: fset.File(astFile.Pos()),
		AST:     astFile,
		Enums:   ext.Enums,
		Matches: ext.Matches,
		matchOf: map[*ast.BadStmt]*MatchStmt{},
	}
	for _, m := range ext.Matches {
		f.matchOf[m.Stmt] = m
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
	for _, e := range ext.Enums {
		e.Gen = specToGen[e.Spec]
		for _, v := range e.Variants {
			if name, ok := directive.Name(v.Doc); ok {
				v.NameOverride = name
			}
		}
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
		if name, ok := directive.Name(fd.Doc); ok {
			gm.NameOverride = name
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
	if name, ok := directive.Name(fd.Doc); ok {
		gm.NameOverride = name
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
