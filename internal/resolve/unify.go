package resolve

import (
	"go/ast"
	"go/parser"

	"goforge.dev/goplus/internal/registry"
)

// Structural GADT unification (v0.6.0). A variant's result arguments are
// arbitrary type expressions over the enum's type parameters; matching,
// construction, and refinement all reduce to unifying those patterns
// against the scrutinee/expected type arguments. This file holds the
// TEXT-level unifier (both sides rendered in the enum package's terms);
// match.go adds the type-level refinement capture on top.

// unifyText unifies a result-arg pattern text against a type-argument
// text, binding the pattern's type parameters (names in tparams) into
// bind. Idents on the ARGUMENT side that are not bindable pattern
// tparams are compared structurally/textually. Returns false on a
// definite structural clash; an underdetermined alignment (pattern
// tparam inside a composite facing an opaque argument ident) also
// returns false — callers treat both as "cannot solve here".
func unifyText(patText, argText string, tparams map[string]bool, bind map[string]string) bool {
	pat, perr := parser.ParseExpr(patText)
	arg, aerr := parser.ParseExpr(argText)
	if perr != nil || aerr != nil {
		return patText == argText
	}
	return unifyExprs(pat, arg, tparams, bind)
}

func unifyExprs(pat, arg ast.Expr, tparams map[string]bool, bind map[string]string) bool {
	if id, ok := pat.(*ast.Ident); ok && tparams[id.Name] {
		text := exprText(arg)
		if prev, bound := bind[id.Name]; bound {
			return prev == text
		}
		bind[id.Name] = text
		return true
	}
	switch p := pat.(type) {
	case *ast.Ident:
		a, ok := arg.(*ast.Ident)
		return ok && a.Name == p.Name
	case *ast.SelectorExpr:
		a, ok := arg.(*ast.SelectorExpr)
		return ok && p.Sel.Name == a.Sel.Name && unifyExprs(p.X, a.X, nil, bind)
	case *ast.StarExpr:
		a, ok := arg.(*ast.StarExpr)
		return ok && unifyExprs(p.X, a.X, tparams, bind)
	case *ast.ArrayType:
		a, ok := arg.(*ast.ArrayType)
		if !ok || (p.Len == nil) != (a.Len == nil) {
			return false
		}
		if p.Len != nil && exprText(p.Len) != exprText(a.Len) {
			return false
		}
		return unifyExprs(p.Elt, a.Elt, tparams, bind)
	case *ast.MapType:
		a, ok := arg.(*ast.MapType)
		return ok && unifyExprs(p.Key, a.Key, tparams, bind) && unifyExprs(p.Value, a.Value, tparams, bind)
	case *ast.ChanType:
		a, ok := arg.(*ast.ChanType)
		return ok && p.Dir == a.Dir && unifyExprs(p.Value, a.Value, tparams, bind)
	case *ast.IndexExpr:
		a, ok := arg.(*ast.IndexExpr)
		return ok && unifyExprs(p.X, a.X, nil, bind) && unifyExprs(p.Index, a.Index, tparams, bind)
	case *ast.IndexListExpr:
		a, ok := arg.(*ast.IndexListExpr)
		if !ok || len(p.Indices) != len(a.Indices) {
			return false
		}
		if !unifyExprs(p.X, a.X, nil, bind) {
			return false
		}
		for i := range p.Indices {
			if !unifyExprs(p.Indices[i], a.Indices[i], tparams, bind) {
				return false
			}
		}
		return true
	case *ast.FuncType:
		a, ok := arg.(*ast.FuncType)
		if !ok {
			return false
		}
		return unifyFieldLists(p.Params, a.Params, tparams, bind) &&
			unifyFieldLists(p.Results, a.Results, tparams, bind)
	case *ast.InterfaceType:
		a, ok := arg.(*ast.InterfaceType)
		return ok && exprText(pat) == exprText(a)
	case *ast.StructType:
		a, ok := arg.(*ast.StructType)
		return ok && exprText(pat) == exprText(a)
	case *ast.ParenExpr:
		return unifyExprs(p.X, arg, tparams, bind)
	}
	if a, ok := arg.(*ast.ParenExpr); ok {
		return unifyExprs(pat, a.X, tparams, bind)
	}
	return exprText(pat) == exprText(arg)
}

func unifyFieldLists(p, a *ast.FieldList, tparams map[string]bool, bind map[string]string) bool {
	pn, an := 0, 0
	var pTypes, aTypes []ast.Expr
	if p != nil {
		for _, f := range p.List {
			c := len(f.Names)
			if c == 0 {
				c = 1
			}
			pn += c
			for i := 0; i < c; i++ {
				pTypes = append(pTypes, f.Type)
			}
		}
	}
	if a != nil {
		for _, f := range a.List {
			c := len(f.Names)
			if c == 0 {
				c = 1
			}
			an += c
			for i := 0; i < c; i++ {
				aTypes = append(aTypes, f.Type)
			}
		}
	}
	if pn != an {
		return false
	}
	for i := range pTypes {
		if !unifyExprs(pTypes[i], aTypes[i], tparams, bind) {
			return false
		}
	}
	return true
}

// variantSubst unifies a variant's result-arg patterns against the
// enum-position type-argument texts, producing the full substitution for
// the variant's type parameters (occurring ones bound structurally,
// eliminated ones grounded from their pattern texts). ok=false when a
// pattern cannot be solved against its argument (clash or
// underdetermined) — the variant cannot be rendered at these arguments.
func variantSubst(e *registry.Enum, v *registry.EnumVariant, targs []string) (map[string]string, bool) {
	bind := map[string]string{}
	if v.ResultArgs == nil {
		for i, n := range e.TParams {
			if i < len(targs) {
				bind[n] = targs[i]
			}
		}
		return bind, true
	}
	tparams := map[string]bool{}
	for _, n := range e.TParams {
		tparams[n] = true
	}
	for i, pat := range v.ResultArgs {
		if !textHasTParam(pat, tparams) {
			continue // ground position: nothing to extract (possibility is filtered elsewhere)
		}
		if i >= len(targs) {
			return nil, false
		}
		if !unifyText(pat, targs[i], tparams, bind) {
			return nil, false
		}
	}
	// Ground positions for eliminated tparams (v0.5.1 subst semantics).
	occursSet := map[int]bool{}
	for _, oi := range v.OccursIn(e) {
		occursSet[oi] = true
	}
	for i, pat := range v.ResultArgs {
		if i < len(e.TParams) && !occursSet[i] {
			if _, bound := bind[e.TParams[i]]; !bound {
				bind[e.TParams[i]] = pat
			}
		}
	}
	// Every occurring tparam must have been determined.
	for _, oi := range v.OccursIn(e) {
		if _, bound := bind[e.TParams[oi]]; !bound {
			return nil, false
		}
	}
	return bind, true
}

// structArgs renders a variant struct's instantiation texts (occurring
// tparams in enum order) from a solved substitution.
func structArgs(e *registry.Enum, v *registry.EnumVariant, bind map[string]string) []string {
	occ := v.OccursIn(e)
	out := make([]string, len(occ))
	for i, oi := range occ {
		out[i] = bind[e.TParams[oi]]
	}
	return out
}

// enumArgsFromBind reconstructs enum-position type-argument texts by
// substituting a solved binding into the variant's result-arg patterns.
func enumArgsFromBind(e *registry.Enum, v *registry.EnumVariant, bind map[string]string) ([]string, bool) {
	if v.ResultArgs == nil {
		out := make([]string, len(e.TParams))
		for i, n := range e.TParams {
			b, bound := bind[n]
			if !bound {
				return nil, false
			}
			out[i] = b
		}
		return out, true
	}
	out := make([]string, len(v.ResultArgs))
	for i, pat := range v.ResultArgs {
		text, err := substTypeTextLite(pat, bind)
		if err != nil {
			return nil, false
		}
		out[i] = text
	}
	return out, true
}

func exprText(e ast.Expr) string {
	return exprString(e)
}

// textHasTParam reports whether a type text mentions any of the names.
func textHasTParam(text string, tparams map[string]bool) bool {
	e, err := parser.ParseExpr(text)
	if err != nil {
		return tparams[text]
	}
	for _, n := range typeIdentNamesExpr(e) {
		if tparams[n] {
			return true
		}
	}
	return false
}

func typeIdentNamesExpr(e ast.Expr) []string {
	var out []string
	ast.Inspect(e, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.SelectorExpr:
			return false
		case *ast.Ident:
			out = append(out, x.Name)
		}
		return true
	})
	return out
}

// laxCompatible reports whether a result-arg pattern could align with a
// type-argument text: pattern tparams and scrutinee-side wildcard names
// match anything; ground leaves compare via groundEq. Used for
// possibility filtering, where underdetermined must count as possible.
func laxCompatible(patText, argText string, patWild, argWild map[string]bool, groundEq func(a, b string) bool) bool {
	pat, perr := parser.ParseExpr(patText)
	arg, aerr := parser.ParseExpr(argText)
	if perr != nil || aerr != nil {
		return patText == argText || groundEq(patText, argText)
	}
	return laxExprs(pat, arg, patWild, argWild, groundEq)
}

func laxExprs(pat, arg ast.Expr, patWild, argWild map[string]bool, groundEq func(a, b string) bool) bool {
	if id, ok := pat.(*ast.Ident); ok && patWild[id.Name] {
		return true
	}
	if id, ok := arg.(*ast.Ident); ok && argWild[id.Name] {
		return true
	}
	switch p := pat.(type) {
	case *ast.StarExpr:
		a, ok := arg.(*ast.StarExpr)
		return ok && laxExprs(p.X, a.X, patWild, argWild, groundEq)
	case *ast.ArrayType:
		a, ok := arg.(*ast.ArrayType)
		return ok && (p.Len == nil) == (a.Len == nil) && laxExprs(p.Elt, a.Elt, patWild, argWild, groundEq)
	case *ast.MapType:
		a, ok := arg.(*ast.MapType)
		return ok && laxExprs(p.Key, a.Key, patWild, argWild, groundEq) && laxExprs(p.Value, a.Value, patWild, argWild, groundEq)
	case *ast.ChanType:
		a, ok := arg.(*ast.ChanType)
		return ok && p.Dir == a.Dir && laxExprs(p.Value, a.Value, patWild, argWild, groundEq)
	case *ast.IndexExpr:
		a, ok := arg.(*ast.IndexExpr)
		return ok && laxExprs(p.X, a.X, nil, nil, groundEq) && laxExprs(p.Index, a.Index, patWild, argWild, groundEq)
	case *ast.IndexListExpr:
		a, ok := arg.(*ast.IndexListExpr)
		if !ok || len(p.Indices) != len(a.Indices) {
			return false
		}
		if !laxExprs(p.X, a.X, nil, nil, groundEq) {
			return false
		}
		for i := range p.Indices {
			if !laxExprs(p.Indices[i], a.Indices[i], patWild, argWild, groundEq) {
				return false
			}
		}
		return true
	}
	pt, at := exprText(pat), exprText(arg)
	return pt == at || groundEq(pt, at)
}
