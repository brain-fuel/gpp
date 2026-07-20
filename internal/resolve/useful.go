package resolve

import (
	"go/token"
	"strings"

	"goforge.dev/goplus/internal/core"
	"goforge.dev/goplus/internal/registry"
	"goforge.dev/goplus/internal/syntax"
)

// Typed pattern usefulness (Maranget's algorithm). With nested patterns a
// per-variant coverage check is wrong — `case Add(Lit(a), _)` does not
// cover Add — so exhaustiveness and reachability both reduce to
// usefulness: a pattern vector is useful w.r.t. a matrix iff some value
// matches it and no earlier row. Exhaustiveness = the all-wildcard vector
// is NOT useful; an arm is unreachable iff its row is not useful w.r.t.
// the rows above. The algorithm also produces a witness for diagnostics.

// patCol describes one matrix column's type: an enum instance (with type
// argument texts) or opaque (only wildcards can match it).
type patCol struct {
	enum     *registry.Enum
	targs    []string
	idxTerms []string  // scrutinee index terms when known (v0.7.0); nil otherwise
	pos      token.Pos // diagnostic anchor (the match subject / parent pattern)
}

// usefulCtx carries the per-match context the engine needs.
type usefulCtx struct {
	r *fileResolver
	// tparamNames: type parameter names in scope at the scrutinee (their
	// occurrences in column targs may be refined, so GADT filtering must
	// treat them as possible).
	tparamNames map[string]bool
	steps       int
	overflow    bool
}

const usefulnessBudget = 100000

// useful reports whether q is useful w.r.t. matrix over cols and, when it
// is, a witness value description.
func (u *usefulCtx) useful(cols []patCol, matrix [][]syntax.PatNode, q []syntax.PatNode) (bool, []syntax.PatNode) {
	u.steps++
	if u.steps > usefulnessBudget {
		u.overflow = true
		return false, nil
	}
	if len(q) == 0 {
		if len(matrix) == 0 {
			return true, nil
		}
		return false, nil
	}
	head := norm(q[0])
	col := cols[0]

	if !head.Wild {
		// Specialize on q's head constructor.
		v, ok := u.variantOf(col, head)
		if !ok {
			return false, nil // pattern names an impossible/unknown variant
		}
		scols, smatrix, sq := u.specialize(cols, matrix, q, v)
		usefulQ, w := u.useful(scols, smatrix, sq)
		if !usefulQ {
			return false, nil
		}
		return true, rebuildWitness(v, len(v.Params), w)
	}

	// q's head is a wildcard.
	if col.enum == nil {
		// Opaque column: only wildcards occur in this column.
		var dmatrix [][]syntax.PatNode
		for _, row := range matrix {
			if norm(row[0]).Wild {
				dmatrix = append(dmatrix, row[1:])
			}
		}
		usefulQ, w := u.useful(cols[1:], dmatrix, q[1:])
		if !usefulQ {
			return false, nil
		}
		return true, append([]syntax.PatNode{{Wild: true}}, w...)
	}

	possible := u.possibleVariants(col)
	rooted := rootConstructors(matrix)
	complete := len(possible) > 0
	for _, v := range possible {
		if !rooted[v.Name] {
			complete = false
		}
	}

	if complete {
		// Every possible variant is rooted: try each specialization.
		for _, v := range possible {
			scols, smatrix, sq := u.specialize(cols, matrix, q, v)
			if ok, w := u.useful(scols, smatrix, sq); ok {
				return true, rebuildWitness(v, len(v.Params), w)
			}
		}
		return false, nil
	}

	// Incomplete signature: the default matrix decides.
	var dmatrix [][]syntax.PatNode
	for _, row := range matrix {
		if norm(row[0]).Wild {
			dmatrix = append(dmatrix, row[1:])
		}
	}
	usefulQ, w := u.useful(cols[1:], dmatrix, q[1:])
	if !usefulQ {
		return false, nil
	}
	// Witness head: some unrooted possible variant, or plain wildcard.
	for _, v := range possible {
		if !rooted[v.Name] {
			return true, append([]syntax.PatNode{witnessNode(v)}, w...)
		}
	}
	return true, append([]syntax.PatNode{{Wild: true}}, w...)
}

// specialize builds the specialized columns, matrix, and query for a
// variant of the first column.
func (u *usefulCtx) specialize(cols []patCol, matrix [][]syntax.PatNode, q []syntax.PatNode, v *registry.EnumVariant) ([]patCol, [][]syntax.PatNode, []syntax.PatNode) {
	arity := len(v.Params)
	fieldCols := u.fieldColumns(cols[0], v)
	scols := append(fieldCols, cols[1:]...)

	expand := func(row []syntax.PatNode) ([]syntax.PatNode, bool) {
		head := norm(row[0])
		if head.Wild {
			wilds := make([]syntax.PatNode, arity)
			for i := range wilds {
				wilds[i] = syntax.PatNode{Wild: true}
			}
			return append(wilds, row[1:]...), true
		}
		hv, ok := u.variantOf(cols[0], head)
		if !ok || hv.Name != v.Name {
			return nil, false
		}
		args := head.Args
		if !head.HasArgs {
			args = nil
		}
		out := make([]syntax.PatNode, 0, arity+len(row)-1)
		for i := 0; i < arity; i++ {
			if i < len(args) {
				out = append(out, args[i])
			} else {
				out = append(out, syntax.PatNode{Wild: true})
			}
		}
		return append(out, row[1:]...), true
	}

	var smatrix [][]syntax.PatNode
	for _, row := range matrix {
		if srow, ok := expand(row); ok {
			smatrix = append(smatrix, srow)
		}
	}
	sq, _ := expand(q)
	return scols, smatrix, sq
}

// fieldColumns derives the column types of a variant's fields under the
// column's instantiation.
func (u *usefulCtx) fieldColumns(col patCol, v *registry.EnumVariant) []patCol {
	subst, sok := variantSubst(col.enum, v, col.targs)
	if !sok {
		return make([]patCol, len(v.Params)) // opaque columns
	}
	out := make([]patCol, len(v.Params))
	for i, p := range v.Params {
		text, err := substTypeTextLite(p.Type, subst)
		if err != nil {
			continue // opaque
		}
		out[i] = u.r.enumColFromTypeText(col.enum.PkgPath, text)
	}
	return out
}

// possibleVariants applies textual GADT filtering to a column.
func (u *usefulCtx) possibleVariants(col patCol) []*registry.EnumVariant {
	var out []*registry.EnumVariant
	for _, v := range col.enum.Variants {
		if u.variantPossibleText(col, v) && !indexRulesOut(u.r.reg, col, v) {
			out = append(out, v)
		}
	}
	return out
}

func (u *usefulCtx) variantPossibleText(col patCol, v *registry.EnumVariant) bool {
	if v.ResultArgs == nil {
		return true
	}
	patWild := map[string]bool{}
	for _, n := range col.enum.TParams {
		patWild[n] = true
	}
	groundEq := func(a, b string) bool {
		if g := u.r.evalInPkg(col.enum.PkgPath, a); g != nil {
			if s := u.r.evalInPkg(col.enum.PkgPath, b); s != nil {
				return typesIdentical(g, s)
			}
		}
		return false
	}
	for i, arg := range v.ResultArgs {
		if i >= len(col.targs) {
			return false
		}
		if !laxCompatible(arg, col.targs[i], patWild, u.tparamNames, groundEq) {
			return false
		}
	}
	return true
}

// variantOf resolves a pattern head against a column's enum.
func (u *usefulCtx) variantOf(col patCol, head syntax.PatNode) (*registry.EnumVariant, bool) {
	if col.enum == nil {
		return nil, false
	}
	if v, ok := col.enum.Variant(head.Name); ok {
		return v, true
	}
	for _, v := range col.enum.Variants {
		if v.TypeName == head.Name {
			return v, true
		}
	}
	return nil, false
}

// rootConstructors collects the variant names appearing at the head of
// matrix rows.
func rootConstructors(matrix [][]syntax.PatNode) map[string]bool {
	out := map[string]bool{}
	for _, row := range matrix {
		if h := norm(row[0]); !h.Wild {
			out[h.Name] = true
		}
	}
	return out
}

// norm treats bare-name binder patterns as wildcards for matching purposes
// only when they are marked as binders during arm analysis; here a bare
// name that reached the matrix is already constructor-resolved, so norm
// only strips nothing. (Binders are normalized before matrix entry.)
func norm(p syntax.PatNode) syntax.PatNode { return p }

func rebuildWitness(v *registry.EnumVariant, arity int, tail []syntax.PatNode) []syntax.PatNode {
	head := syntax.PatNode{Name: v.Name, HasArgs: arity > 0}
	for i := 0; i < arity && i < len(tail); i++ {
		head.Args = append(head.Args, tail[i])
	}
	rest := tail
	if arity <= len(tail) {
		rest = tail[arity:]
	} else {
		rest = nil
	}
	return append([]syntax.PatNode{head}, rest...)
}

func witnessNode(v *registry.EnumVariant) syntax.PatNode {
	n := syntax.PatNode{Name: v.Name, HasArgs: len(v.Params) > 0}
	for range v.Params {
		n.Args = append(n.Args, syntax.PatNode{Wild: true})
	}
	return n
}

// renderWitness renders a witness vector's single root pattern.
func renderWitness(w []syntax.PatNode) string {
	if len(w) == 0 {
		return "_"
	}
	parts := make([]string, len(w))
	for i, n := range w {
		parts[i] = n.String()
	}
	return strings.Join(parts, ", ")
}

// indexRulesOut reports whether the column's known index terms make a
// variant impossible (v0.7.0).
func indexRulesOut(reg *registry.Registry, col patCol, v *registry.EnumVariant) bool {
	if len(col.idxTerms) == 0 || len(v.IndexArgs) != len(col.idxTerms) {
		return false
	}
	tagOf := registryTagOf(reg, col.enum)
	for i := range col.idxTerms {
		if core.IndexClash(col.idxTerms[i], v.IndexArgs[i], tagOf) {
			return true
		}
	}
	return false
}

// registryTagOf builds a tag table over the enum's index-domain sorts.
func registryTagOf(reg *registry.Registry, e *registry.Enum) func(string) (string, bool) {
	return func(name string) (string, bool) {
		for _, ib := range e.Indices {
			if ib.Sort == "nat" {
				continue
			}
			domPkg := e.PkgPath
			if ib.SortPkg != "" {
				domPkg = ib.SortPkg
			}
			dom, ok := reg.LookupEnum(domPkg, registry.SortBase(ib.Sort))
			if !ok {
				continue
			}
			for _, v := range dom.Variants {
				if v.Name == name {
					return ib.Sort, true
				}
			}
		}
		return "", false
	}
}
