package resolve

import (
	"go/ast"
	"go/token"
	"go/types"
	"regexp"
	"strings"

	"goforge.dev/goplus/internal/lower"
)

// Expression-form temp typing (v0.4.0 Engine B). Pass 1 hoists an
// expression if/switch/match to statements assigning `__gp_vN = arm`
// behind a type-deferred decl `__gp_vN := __gp_valN()`. Resolution picks
// the temp's type — the context's expected type first, otherwise the arms'
// shared default type — and rewrites the decl to `var __gp_vN T`.

var valTempName = regexp.MustCompile(`^__gp_v\d+$`)

// exprformCandidate types one temp decl carrier.
func (r *fileResolver) exprformCandidate(as *ast.AssignStmt) {
	name, ok := valDeclName(as)
	if !ok {
		return
	}
	info := r.pkg.TypesInfo

	// Every arm assignment must be typed before the temp commits: arms
	// inside unresolved match skeletons (undefined binders) or containing
	// carriers wait for a later iteration.
	assigns := r.tempAssignments(name)
	if len(assigns) == 0 {
		if r.report {
			r.errorf(as.Pos(), "internal error: expression-form temp %s has no arm assignments", name)
		}
		return
	}
	var armTypes []types.Type
	for _, a := range assigns {
		tv, typed := info.Types[a.Rhs[0]]
		if !typed || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
			if r.report {
				r.errorf(a.Rhs[0].Pos(), "cannot resolve this expression arm: its type is unknown")
			}
			return
		}
		armTypes = append(armTypes, types.Default(tv.Type))
	}

	T := r.tempExpectedType(name, as)
	if T == nil {
		T = armTypes[0]
		for _, at := range armTypes[1:] {
			if !types.Identical(T, at) {
				if r.report {
					r.errorf(as.Pos(),
						"mismatched arm types in this expression form: %s vs %s; make the arms agree or let the context determine the type (assign to a declared variable, return, or pass as a typed argument)",
						r.localTypeString(T), r.localTypeString(at))
				}
				return
			}
		}
	}

	text, err := r.typeText(T)
	if err != nil {
		r.errorf(as.Pos(), "%v", err)
		return
	}
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(as.Pos()),
		End:   r.off(as.End()),
		New:   "var " + name + " " + text,
	})
}

// valDeclName recognizes `__gp_vN := __gp_valN()`.
func valDeclName(as *ast.AssignStmt) (string, bool) {
	if as.Tok != token.DEFINE || len(as.Lhs) != 1 || len(as.Rhs) != 1 {
		return "", false
	}
	lhs, ok := as.Lhs[0].(*ast.Ident)
	if !ok || !valTempName.MatchString(lhs.Name) {
		return "", false
	}
	call, ok := as.Rhs[0].(*ast.CallExpr)
	if !ok || len(call.Args) != 0 {
		return "", false
	}
	fn, ok := call.Fun.(*ast.Ident)
	if !ok || !strings.HasPrefix(fn.Name, lower.ValCarrierPrefix) {
		return "", false
	}
	return lhs.Name, true
}

// tempAssignments collects the temp's arm assignments (`__gp_vN = expr`).
func (r *fileResolver) tempAssignments(name string) []*ast.AssignStmt {
	var out []*ast.AssignStmt
	ast.Inspect(r.file, func(n ast.Node) bool {
		a, ok := n.(*ast.AssignStmt)
		if !ok || a.Tok != token.ASSIGN || len(a.Lhs) != 1 || len(a.Rhs) != 1 {
			return true
		}
		if id, isID := a.Lhs[0].(*ast.Ident); isID && id.Name == name {
			out = append(out, a)
		}
		return true
	})
	return out
}

// tempTargetType resolves the type an expression-form temp carries: its
// declared type once the decl carrier is rewritten, else the type its use
// site expects (the decl may still be a carrier when a refined match arm
// needs the target type).
func (r *fileResolver) tempTargetType(name string) types.Type {
	info := r.pkg.TypesInfo
	var T types.Type
	ast.Inspect(r.file, func(n ast.Node) bool {
		if T != nil {
			return false
		}
		id, ok := n.(*ast.Ident)
		if !ok || id.Name != name {
			return true
		}
		if obj := info.ObjectOf(id); obj != nil && obj.Type() != nil && obj.Type() != types.Typ[types.Invalid] {
			T = obj.Type()
		}
		return true
	})
	if T == nil {
		T = r.tempExpectedType(name, nil)
	}
	return T
}

// tempExpectedType finds the type the temp's use site expects, if any.
// Uses exclude the decl and the arm-assignment targets.
func (r *fileResolver) tempExpectedType(name string, decl *ast.AssignStmt) types.Type {
	var T types.Type
	ast.Inspect(r.file, func(n ast.Node) bool {
		if T != nil {
			return false
		}
		id, ok := n.(*ast.Ident)
		if !ok || id.Name != name {
			return true
		}
		switch p := r.parents[id].(type) {
		case *ast.AssignStmt:
			if p == decl || (p.Tok == token.ASSIGN && len(p.Lhs) == 1 && p.Lhs[0] == id) {
				return true
			}
		}
		if t := r.expectedType(id); t != nil && t != types.Typ[types.Invalid] {
			T = t
		}
		return false
	})
	return T
}
