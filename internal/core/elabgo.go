package core

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"math/big"
)

// Elaboration of total-function bodies from Go syntax (v0.7.0). The
// admitted fragment is deliberately small: if/else and return over nat
// expressions built from parameters, integer literals, + - *, parens,
// and calls to total functions. The SAME elaborator serves the original
// .gpp declaration (gen pass 1) and the erased Go body behind a
// //gpp:total marker (registry reconstruction) — the generated body is
// the definition.

// CallResolver canonicalizes a callee expression to the registry key
// "pkgpath.Name" (local names resolve against the defining package).
type CallResolver func(fun ast.Expr) (string, bool)

// ElabFuncBody elaborates one total function.
func ElabFuncBody(name string, params []string, body *ast.BlockStmt, resolve CallResolver) (*Def, error) {
	if body == nil {
		return nil, fmt.Errorf("total function %s has no body", name)
	}
	e := &elaborator{resolve: resolve}
	t, err := e.block(body.List)
	if err != nil {
		return nil, fmt.Errorf("total function %s: %w", name, err)
	}
	return &Def{Name: name, Params: params, Body: t}, nil
}

type elaborator struct {
	resolve CallResolver
}

// block elaborates a statement list that must end every path in return.
func (e *elaborator) block(stmts []ast.Stmt) (Term, error) {
	if len(stmts) == 0 {
		return nil, fmt.Errorf("every path in a total function must return")
	}
	switch s := stmts[0].(type) {
	case *ast.ReturnStmt:
		if len(stmts) > 1 {
			return nil, fmt.Errorf("unreachable statements after return")
		}
		if len(s.Results) != 1 {
			return nil, fmt.Errorf("a total function returns exactly one nat")
		}
		return e.expr(s.Results[0])
	case *ast.IfStmt:
		if s.Init != nil {
			return nil, fmt.Errorf("if with an init statement is outside the total fragment (v0.7.0 allows if/return over nat expressions)")
		}
		op, l, r, err := e.cond(s.Cond)
		if err != nil {
			return nil, err
		}
		then, err := e.block(s.Body.List)
		if err != nil {
			return nil, err
		}
		var els Term
		switch rest := s.Else.(type) {
		case nil:
			if len(stmts) < 2 {
				return nil, fmt.Errorf("every path in a total function must return")
			}
			els, err = e.block(stmts[1:])
		case *ast.BlockStmt:
			if len(stmts) > 1 {
				return nil, fmt.Errorf("unreachable statements after if/else")
			}
			els, err = e.block(rest.List)
		case *ast.IfStmt:
			if len(stmts) > 1 {
				return nil, fmt.Errorf("unreachable statements after if/else")
			}
			els, err = e.block([]ast.Stmt{rest})
		default:
			return nil, fmt.Errorf("unsupported else form in a total function")
		}
		if err != nil {
			return nil, err
		}
		return If{Op: op, L: l, R: r, Then: then, Else: els}, nil
	default:
		return nil, fmt.Errorf("%T is outside the total fragment (v0.7.0 allows if/return over nat expressions)", stmts[0])
	}
}

func (e *elaborator) cond(c ast.Expr) (string, Term, Term, error) {
	b, ok := c.(*ast.BinaryExpr)
	if !ok {
		return "", nil, nil, fmt.Errorf("a total function's condition must be a nat comparison")
	}
	switch b.Op {
	case token.EQL, token.NEQ, token.LSS, token.LEQ, token.GTR, token.GEQ:
	default:
		return "", nil, nil, fmt.Errorf("a total function's condition must be a nat comparison, not %s", b.Op)
	}
	l, err := e.expr(b.X)
	if err != nil {
		return "", nil, nil, err
	}
	r, err := e.expr(b.Y)
	if err != nil {
		return "", nil, nil, err
	}
	return b.Op.String(), l, r, nil
}

func (e *elaborator) expr(x ast.Expr) (Term, error) {
	switch v := x.(type) {
	case *ast.Ident:
		return Var{Name: v.Name}, nil
	case *ast.BasicLit:
		if v.Kind != token.INT {
			return nil, fmt.Errorf("literal %s is not a nat", v.Value)
		}
		n := new(big.Int)
		if _, ok := n.SetString(v.Value, 0); !ok {
			return nil, fmt.Errorf("cannot parse nat literal %s", v.Value)
		}
		return Nat{N: n}, nil
	case *ast.ParenExpr:
		return e.expr(v.X)
	case *ast.BinaryExpr:
		switch v.Op {
		case token.ADD, token.SUB, token.MUL:
		default:
			return nil, fmt.Errorf("operator %s is outside the total fragment (nat has + - *)", v.Op)
		}
		l, err := e.expr(v.X)
		if err != nil {
			return nil, err
		}
		r, err := e.expr(v.Y)
		if err != nil {
			return nil, err
		}
		return Prim{Op: v.Op.String(), Args: []Term{l, r}}, nil
	case *ast.CallExpr:
		key, ok := e.resolve(v.Fun)
		if !ok {
			return nil, fmt.Errorf("only total functions may be called in a total function body")
		}
		args := make([]Term, len(v.Args))
		for i, a := range v.Args {
			t, err := e.expr(a)
			if err != nil {
				return nil, err
			}
			args[i] = t
		}
		return Call{Fn: key, Args: args}, nil
	}
	return nil, fmt.Errorf("%T is outside the total fragment (v0.7.0 allows nat expressions: parameters, literals, + - *, and total calls)", x)
}

// ElabIndexExpr elaborates a standalone index-term expression (a result
// or field index argument of an indexed enum).
func ElabIndexExpr(x ast.Expr, resolve CallResolver) (Term, error) {
	e := &elaborator{resolve: resolve}
	return e.expr(x)
}

// ParseIndexTerm elaborates an index term from its source text (marker
// reconstruction: terms cannot round-trip through go/parser in type
// position, but stand alone they are ordinary expressions).
func ParseIndexTerm(text string, resolve CallResolver) (Term, error) {
	x, err := parser.ParseExpr(text)
	if err != nil {
		return nil, fmt.Errorf("cannot parse index term %q: %v", text, err)
	}
	return ElabIndexExpr(x, resolve)
}
