package gen

import (
	"go/ast"

	"goforge.dev/goplus/internal/lower"
	"goforge.dev/goplus/internal/registry"
)

// Ordinary-position index erasure (v0.7.0). Outside enum declarations,
// instantiations of indexed enums (`var v Vec[int, 2]`, params,
// results, conversions) drop their index arguments in the generated Go.
// Two complementary walks:
//
//   - EXACT: instantiations of same-package indexed enums erase
//     precisely, in any position, by declared index positions.
//   - TYPE-POSITION: inside a syntactic type (param, result, field,
//     var, composite-literal type, type assertion), a TERM-shaped
//     argument (literal, arithmetic, call) can never be valid Go, so it
//     is an index argument of an enum pass 1 cannot name — usually an
//     imported one — and drops. Bare-ident index args survive (they
//     parse as type args) for resolve's registry-aware candidate.
//
// Index checking at these boundaries is the dependent-signature layer's
// work; erasure alone keeps the shadow world well-typed.

// eraseOrdinaryIndexUses rewrites index-carrying instantiations in one
// file's ordinary code.
func eraseOrdinaryIndexUses(f *sourceFile, isIndexed registry.IndexArity) []lower.Edit {
	var edits []lower.Edit
	src := f.gp

	drop := func(args []ast.Expr, idxPos map[int]bool, lbrack, rbrack int) {
		kept := 0
		for i := range args {
			if !idxPos[i] {
				kept++
			}
		}
		if kept == 0 {
			edits = append(edits, lower.Edit{Start: lbrack, End: rbrack + 1, New: ""})
			return
		}
		for i, a := range args {
			if !idxPos[i] {
				continue
			}
			if i+1 < len(args) {
				edits = append(edits, lower.Edit{Start: src.Offset(a.Pos()), End: src.Offset(args[i+1].Pos()), New: ""})
			} else {
				edits = append(edits, lower.Edit{Start: src.Offset(args[i-1].End()), End: src.Offset(a.End()), New: ""})
			}
		}
	}

	decompose := func(n ast.Node) (base ast.Expr, args []ast.Expr, lbrack, rbrack int, ok bool) {
		switch x := n.(type) {
		case *ast.IndexExpr:
			return x.X, []ast.Expr{x.Index}, src.Offset(x.Lbrack), src.Offset(x.Rbrack), true
		case *ast.IndexListExpr:
			return x.X, x.Indices, src.Offset(x.Lbrack), src.Offset(x.Rbrack), true
		}
		return nil, nil, 0, 0, false
	}
	baseName := func(base ast.Expr) string {
		switch b := base.(type) {
		case *ast.Ident:
			return b.Name
		case *ast.SelectorExpr:
			return b.Sel.Name
		}
		return ""
	}

	handled := map[ast.Node]bool{}

	// Walk 1 — exact erasure for known indexed enums, any position.
	ast.Inspect(f.gp.AST, func(n ast.Node) bool {
		base, args, lbrack, rbrack, ok := decompose(n)
		if !ok {
			return true
		}
		idxPos, arity, known := isIndexed(baseName(base))
		if !known || len(args) != arity {
			return true
		}
		handled[n] = true
		drop(args, idxPos, lbrack, rbrack)
		return true
	})

	// Walk 2 — term-shaped arguments inside syntactic type positions.
	inType := func(root ast.Expr) {
		if root == nil {
			return
		}
		ast.Inspect(root, func(n ast.Node) bool {
			base, args, lbrack, rbrack, ok := decompose(n)
			if !ok || handled[n] {
				return true
			}
			if baseName(base) == "Eq" {
				return true // proof propositions live only in dropped params
			}
			if _, _, known := isIndexed(baseName(base)); known {
				return true // walk 1's business (arity mismatch = already erased)
			}
			idxPos := map[int]bool{}
			for i, a := range args {
				if termShaped(a) {
					idxPos[i] = true
				}
			}
			if len(idxPos) == 0 {
				return true
			}
			// All-term arguments in a type position lose the brackets
			// entirely: the enum's erased form has no type parameters.
			handled[n] = true
			drop(args, idxPos, lbrack, rbrack)
			return true
		})
	}
	fieldList := func(fl *ast.FieldList) {
		if fl == nil {
			return
		}
		for _, fld := range fl.List {
			inType(fld.Type)
		}
	}
	ast.Inspect(f.gp.AST, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.FuncDecl:
			if x.Type != nil {
				fieldList(x.Type.Params)
				fieldList(x.Type.Results)
			}
		case *ast.FuncLit:
			fieldList(x.Type.Params)
			fieldList(x.Type.Results)
		case *ast.ValueSpec:
			inType(x.Type)
		case *ast.TypeSpec:
			inType(x.Type)
		case *ast.CompositeLit:
			inType(x.Type)
		case *ast.TypeAssertExpr:
			inType(x.Type)
		}
		return true
	})
	return edits
}

// termShaped reports whether an instantiation argument can only be a
// value-level term (never a type): literals, arithmetic, calls.
func termShaped(e ast.Expr) bool {
	switch x := e.(type) {
	case *ast.BasicLit:
		return true
	case *ast.BinaryExpr:
		return true
	case *ast.CallExpr:
		return true
	case *ast.ParenExpr:
		return termShaped(x.X)
	}
	return false
}
