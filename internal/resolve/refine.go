package resolve

import (
	"go/ast"
	"go/token"
	"go/types"
	"sort"
	"strings"

	"goforge.dev/gpp/internal/lower"
)

// Type-directed GADT refinement (v0.6.0). Match resolution cannot type an
// arm's body in its own iteration (the bindings land in the same edit),
// so it leaves a carrier at the top of each refined arm:
//
//	//gpp:refine T=int	U=Pair[A, B]
//
// One iteration later the bindings exist and the body types; this
// candidate then wraps every MISMATCHED conversion boundary in the arm's
// scope — returns, assignments, call arguments, composite literals, and
// the other expectedType contexts — as any(E).(C) whenever the refined
// substitution reconciles the actual and required types. Both directions
// wrap (ground→T and T→ground). The walk stops at function literals.
// Idempotent: a wrapped expression's type becomes the required type.

// RefineCarrier is the carrier comment prefix.
const RefineCarrier = "//gpp:refine "

// refineCarrierLine renders a carrier for a refined-arm binding set,
// deterministically ordered, tab-separated (type texts never contain
// tabs).
func refineCarrierLine(refined map[string]string) string {
	keys := make([]string, 0, len(refined))
	for k := range refined {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	parts := make([]string, len(keys))
	for i, k := range keys {
		parts[i] = k + "=" + refined[k]
	}
	return RefineCarrier + strings.Join(parts, "\t")
}

// refineCandidates scans the file's comments for refine carriers and
// processes each. Called once per iteration from resolve().
func (r *fileResolver) refineCandidates() {
	for _, cg := range r.file.Comments {
		for _, c := range cg.List {
			if !strings.HasPrefix(c.Text, RefineCarrier) {
				continue
			}
			r.refineOne(c)
		}
	}
}

// refineOne processes one carrier: when every expression in scope is
// typed (or on the audit pass), it emits the wraps and deletes the
// carrier line.
func (r *fileResolver) refineOne(c *ast.Comment) {
	refined := map[string]string{}
	rest := strings.TrimPrefix(c.Text, RefineCarrier)
	for _, pair := range strings.Split(rest, "\t") {
		if eq := strings.Index(pair, "="); eq > 0 {
			refined[pair[:eq]] = pair[eq+1:]
		}
	}
	if len(refined) == 0 {
		r.deleteCarrierLine(c)
		return
	}

	stmts := r.carrierScope(c)
	if stmts == nil {
		if r.report {
			r.deleteCarrierLine(c)
		}
		return
	}

	info := r.pkg.TypesInfo
	ready := true
	var wraps []lower.Edit
	seenWrap := map[ast.Expr]bool{}

	var walk func(n ast.Node)
	walk = func(n ast.Node) {
		ast.Inspect(n, func(x ast.Node) bool {
			if _, isLit := x.(*ast.FuncLit); isLit {
				return false
			}
			e, isExpr := x.(ast.Expr)
			if !isExpr {
				return true
			}
			if seenWrap[e] {
				return false // outermost wrap wins
			}
			tv, typed := info.Types[e]
			if typed && tv.IsType() {
				return false // type expressions have no conversion boundary
			}
			if !typed || tv.Type == nil {
				return true
			}
			if tv.Type == types.Typ[types.Invalid] {
				ready = false
				return true
			}
			C := r.expectedType(e)
			if C == nil || C == types.Typ[types.Invalid] {
				// An assignment RHS whose LHS is not yet typed (an
				// expression-form temp still behind its carrier) is a
				// boundary we cannot judge yet — wait, don't skip.
				if as, isAssign := r.parents[e].(*ast.AssignStmt); isAssign && as.Tok == token.ASSIGN {
					for i, rhs := range as.Rhs {
						if rhs == e && i < len(as.Lhs) {
							ltv, lok := info.Types[as.Lhs[i]]
							if !lok || ltv.Type == nil || ltv.Type == types.Typ[types.Invalid] {
								ready = false
							}
						}
					}
				}
				return true
			}
			A := types.Default(tv.Type)
			if types.AssignableTo(A, C) {
				return true
			}
			if !r.refineReconciles(c.Pos(), A, C, refined) {
				return true
			}
			cText, err := r.typeText(C)
			if err != nil {
				return true
			}
			eText := r.text(e.Pos(), e.End())
			wraps = append(wraps, lower.Edit{
				Start: r.off(e.Pos()),
				End:   r.off(e.End()),
				New:   "any(" + eText + ").(" + cText + ")",
			})
			seenWrap[e] = true
			return false
		})
	}
	for _, st := range stmts {
		walk(st)
	}

	if !ready && !r.report {
		return // some expression is untyped; retry next iteration
	}
	r.edits = append(r.edits, wraps...)
	r.deleteCarrierLine(c)
}

// refineReconciles reports whether substituting the refined type
// parameters into both sides makes the actual type identical to the
// required type.
func (r *fileResolver) refineReconciles(at token.Pos, A, C types.Type, refined map[string]string) bool {
	aText, aerr := r.typeText(A)
	cText, cerr := r.typeText(C)
	if aerr != nil || cerr != nil {
		return false
	}
	aSub, aerr2 := substTypeTextLite(aText, refined)
	cSub, cerr2 := substTypeTextLite(cText, refined)
	if aerr2 != nil || cerr2 != nil {
		return false
	}
	if aSub == aText && cSub == cText {
		return false // neither side mentions a refined parameter
	}
	if aSub == cSub {
		return true
	}
	ta, err1 := types.Eval(r.pkg.Fset, r.pkg.Types, at, aSub)
	tc, err2 := types.Eval(r.pkg.Fset, r.pkg.Types, at, cSub)
	if err1 != nil || err2 != nil || ta.Type == nil || tc.Type == nil {
		return false
	}
	return types.AssignableTo(ta.Type, tc.Type)
}

// carrierScope finds the statements the carrier governs: those of the
// innermost enclosing block strictly after the carrier line.
func (r *fileResolver) carrierScope(c *ast.Comment) []ast.Stmt {
	pos := r.off(c.Pos())
	var best []ast.Stmt
	bestSize := 1 << 62
	consider := func(list []ast.Stmt, from, to token.Pos) {
		f, t := r.off(from), r.off(to)
		if f <= pos && pos <= t && t-f < bestSize {
			var after []ast.Stmt
			for _, st := range list {
				if r.off(st.Pos()) > pos {
					after = append(after, st)
				}
			}
			best, bestSize = after, t-f
		}
	}
	ast.Inspect(r.file, func(n ast.Node) bool {
		switch b := n.(type) {
		case *ast.BlockStmt:
			consider(b.List, b.Lbrace, b.Rbrace)
		case *ast.CaseClause:
			if len(b.Body) > 0 {
				consider(b.Body, b.Colon, b.Body[len(b.Body)-1].End())
			}
		case *ast.CommClause:
			if len(b.Body) > 0 {
				consider(b.Body, b.Colon, b.Body[len(b.Body)-1].End())
			}
		}
		return true
	})
	return best
}

// deleteCarrierLine removes the carrier comment's whole line.
func (r *fileResolver) deleteCarrierLine(c *ast.Comment) {
	start := r.off(c.Pos())
	for start > 0 && r.src[start-1] != '\n' {
		start--
	}
	end := r.off(c.End())
	if end < len(r.src) && r.src[end] == '\n' {
		end++
	}
	r.edits = append(r.edits, lower.Edit{Start: start, End: end, New: ""})
}
