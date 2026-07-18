package resolve

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"strings"

	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/registry"
)

// Constructor resolution. G++ constructs variants call-style (Some(41),
// None) or qualified (Option.None, Option[int].Some(x)); all forms are
// already valid Go syntax. Each use lowers to a named-field composite
// literal of the variant struct. Type arguments come from explicit
// instantiation, the expected type of the surrounding context, or
// structural unification of declared parameter types against argument
// types. Bare names shared by several enums are resolved by that same
// inference; only genuinely ambiguous uses demand qualification. In value
// position with a function-typed expected type, a constructor auto-wraps
// into a closure.

// ctorUse is one candidate reading of a constructor use.
type ctorUse struct {
	enum    *registry.Enum
	variant *registry.EnumVariant

	name ast.Expr // the Ident or SelectorExpr naming the constructor
	full ast.Expr // name plus any explicit instantiation
	call *ast.CallExpr

	explicit []ast.Expr // explicit type argument exprs, nil if none
	pkgAlias string     // file-local package qualifier for cross-package enums
}

// ctorCandidate inspects an identifier or selector that may name a
// variant constructor; inference picks among candidate enums.
func (r *fileResolver) ctorCandidate(name ast.Expr) {
	cands := r.recognizeCtors(name)
	if len(cands) == 0 {
		return
	}
	type resolvedUse struct {
		use   *ctorUse
		targs []string
	}
	var oks []resolvedUse
	for _, u := range cands {
		if targs, ok := r.inferTargs(u); ok {
			oks = append(oks, resolvedUse{u, targs})
		}
	}
	switch {
	case len(oks) == 1:
		r.finishCtor(oks[0].use, oks[0].targs)
	case !r.report:
		// Not resolvable yet; a later iteration (or the audit) decides.
	case len(oks) > 1 || len(cands) > 1:
		var names []string
		for _, u := range cands {
			names = append(names, u.enum.Name)
		}
		u := cands[0]
		r.errorf(name.Pos(), "constructor %s is declared by %s; qualify it: %s.%s",
			u.variant.Name, strings.Join(names, " and "), u.enum.Name, u.variant.Name)
	default:
		r.ctorGiveUp(cands[0])
	}
}

// recognizeCtors classifies a name expression, returning every candidate
// reading (bare names shared across enums yield several).
func (r *fileResolver) recognizeCtors(name ast.Expr) []*ctorUse {
	info := r.pkg.TypesInfo
	var bases []*ctorUse

	switch n := name.(type) {
	case *ast.Ident:
		// Skip the Sel of a selector (the parent handles it) and any
		// ident that already resolves to a non-type object (shadowing).
		if sel, ok := r.parents[n].(*ast.SelectorExpr); ok && sel.Sel == n {
			return nil
		}
		switch obj := info.Uses[n].(type) {
		case *types.TypeName:
			// Direct spelling of a lowered variant struct type.
			if obj.Pkg() == nil || obj.Pkg().Path() != r.pkg.PkgPath {
				return nil
			}
			if e, ok := r.reg.EnumByVariantType(obj.Pkg().Path(), obj.Name()); ok {
				bases = append(bases, &ctorUse{enum: e, variant: variantByTypeName(e, obj.Name()), name: n})
			}
		case nil:
			if info.Defs[n] != nil {
				return nil
			}
			// Unresolved: a G++ variant name whose lowered struct is
			// prefixed or renamed. Every declaring enum is a candidate.
			for _, e := range r.reg.EnumsByVariantName(r.pkg.PkgPath, n.Name) {
				if v, ok := e.Variant(n.Name); ok {
					bases = append(bases, &ctorUse{enum: e, variant: v, name: n})
				}
			}
		default:
			return nil
		}
	case *ast.SelectorExpr:
		if u, ok := r.recognizeQualified(n); ok {
			bases = append(bases, u)
		}
	}

	var out []*ctorUse
	for _, u := range bases {
		if u.variant == nil {
			continue
		}
		full := ast.Expr(u.name)
		if u.explicit == nil {
			switch p := r.parents[full].(type) {
			case *ast.IndexExpr:
				if p.X == full {
					u.explicit = []ast.Expr{p.Index}
					full = p
				}
			case *ast.IndexListExpr:
				if p.X == full {
					u.explicit = p.Indices
					full = p
				}
			}
		}
		u.full = full
		if call, ok := r.parents[full].(*ast.CallExpr); ok && call.Fun == full {
			u.call = call
		}
		if r.isExprPosition(u.outermost()) {
			out = append(out, u)
		}
	}
	return out
}

// recognizeQualified handles selector-based spellings: pkg.Variant,
// Enum.Variant, Enum[T].Variant, pkg.Enum.Variant, pkg.Enum[T].Variant.
func (r *fileResolver) recognizeQualified(sel *ast.SelectorExpr) (*ctorUse, bool) {
	info := r.pkg.TypesInfo
	use := &ctorUse{name: sel}

	// Case A: X names a package; Sel is a lowered variant struct type.
	if pkgID, ok := sel.X.(*ast.Ident); ok {
		if _, isPkg := info.Uses[pkgID].(*types.PkgName); isPkg {
			tn, _ := info.Uses[sel.Sel].(*types.TypeName)
			if tn == nil || tn.Pkg() == nil {
				return nil, false
			}
			e, ok := r.reg.EnumByVariantType(tn.Pkg().Path(), tn.Name())
			if !ok {
				return nil, false
			}
			use.enum, use.variant, use.pkgAlias = e, variantByTypeName(e, tn.Name()), pkgID.Name
			return use, use.variant != nil
		}
	}

	// Case B: X (possibly instantiated, possibly pkg-qualified) names an
	// enum; Sel is the G++ variant name.
	base := sel.X
	switch x := base.(type) {
	case *ast.IndexExpr:
		use.explicit = []ast.Expr{x.Index}
		base = x.X
	case *ast.IndexListExpr:
		use.explicit = x.Indices
		base = x.X
	}
	tn, alias := resolveTypeNameOf(info, base)
	if tn == nil || tn.Pkg() == nil {
		return nil, false
	}
	e, ok := r.reg.LookupEnum(tn.Pkg().Path(), tn.Name())
	if !ok {
		return nil, false
	}
	v, ok := e.Variant(sel.Sel.Name)
	if !ok {
		return nil, false
	}
	use.enum, use.variant, use.pkgAlias = e, v, alias
	return use, true
}

func resolveTypeNameOf(info *types.Info, e ast.Expr) (*types.TypeName, string) {
	switch x := e.(type) {
	case *ast.Ident:
		tn, _ := info.Uses[x].(*types.TypeName)
		return tn, ""
	case *ast.SelectorExpr:
		if pkgID, ok := x.X.(*ast.Ident); ok {
			if _, isPkg := info.Uses[pkgID].(*types.PkgName); isPkg {
				tn, _ := info.Uses[x.Sel].(*types.TypeName)
				return tn, pkgID.Name
			}
		}
	}
	return nil, ""
}

func variantByTypeName(e *registry.Enum, typeName string) *registry.EnumVariant {
	for _, v := range e.Variants {
		if v.TypeName == typeName {
			return v
		}
	}
	return nil
}

// outermost returns the widest expression this use rewrites.
func (u *ctorUse) outermost() ast.Expr {
	if u.call != nil {
		return u.call
	}
	return u.full
}

// isExprPosition reports whether e sits where an expression (not a type)
// is expected — a whitelist over parent contexts, so type references like
// `var x Some[int]` and switch case types are never rewritten.
func (r *fileResolver) isExprPosition(e ast.Expr) bool {
	switch p := r.parents[e].(type) {
	case *ast.CallExpr:
		return true // Fun of a nested constructor call, or an argument
	case *ast.AssignStmt, *ast.ReturnStmt, *ast.ExprStmt, *ast.SendStmt,
		*ast.BinaryExpr, *ast.IncDecStmt, *ast.GoStmt, *ast.DeferStmt,
		*ast.RangeStmt, *ast.IfStmt, *ast.ForStmt, *ast.SwitchStmt:
		return true
	case *ast.KeyValueExpr:
		return p.Value == e
	case *ast.CompositeLit:
		return p.Type != e
	case *ast.ValueSpec:
		return p.Type != e
	case *ast.ParenExpr:
		return r.isExprPosition(p)
	case *ast.UnaryExpr:
		return true
	case *ast.IndexExpr:
		return p.Index == e // only as an index expression
	}
	return false
}

// inferTargs determines one type-argument text per enum type parameter,
// or reports that this reading cannot (yet) be resolved.
func (r *fileResolver) inferTargs(use *ctorUse) ([]string, bool) {
	e, v := use.enum, use.variant
	if len(use.explicit) > 0 {
		return r.explicitTargs(use)
	}
	// Ground positions are fixed by the variant's declared result type.
	targs := make([]string, len(e.TParams))
	filled := 0
	if v.ResultArgs != nil {
		kept := keptSet(e, v)
		for i, arg := range v.ResultArgs {
			if !kept[i] {
				targs[i] = arg
				filled++
			}
		}
	}
	if filled == len(e.TParams) {
		return targs, true
	}
	if got, ok := r.targsFromExpected(use, targs); ok {
		return got, true
	}
	if use.call != nil {
		if got, ok := r.targsFromArgs(use, targs); ok {
			return got, true
		}
	}
	return nil, false
}

// finishCtor emits the rewrite for the single successful reading.
func (r *fileResolver) finishCtor(use *ctorUse, targs []string) {
	v := use.variant
	if use.call == nil {
		if sig := r.expectedFuncSig(use); sig != nil {
			r.wrapCtor(use, targs, sig)
			return
		}
		if len(v.Params) > 0 {
			r.errorf(use.name.Pos(), "constructor %s requires arguments; call it or use it where a function value is expected", v.Name)
			return
		}
		r.emitCtor(use, targs, nil)
		return
	}
	if len(use.call.Args) != len(v.Params) {
		r.errorf(use.name.Pos(), "constructor %s expects %d arguments, got %d", v.Name, len(v.Params), len(use.call.Args))
		return
	}
	argTexts := make([]string, len(use.call.Args))
	for i, a := range use.call.Args {
		argTexts[i] = r.text(a.Pos(), a.End())
	}
	if use.call.Ellipsis.IsValid() {
		r.errorf(use.call.Ellipsis, "constructor arguments cannot be spread with ...")
		return
	}
	r.emitCtor(use, targs, argTexts)
}

// emitCtor rewrites the use to a composite literal.
func (r *fileResolver) emitCtor(use *ctorUse, targs, argTexts []string) {
	litType, ok := r.ctorTypeText(use, targs)
	if !ok {
		return
	}
	var b strings.Builder
	b.WriteString(litType)
	b.WriteString("{")
	for i, at := range argTexts {
		if i > 0 {
			b.WriteString(", ")
		}
		b.WriteString(use.variant.Params[i].FieldName + ": " + at)
	}
	b.WriteString("}")
	out := use.outermost()
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(out.Pos()),
		End:   r.off(out.End()),
		New:   b.String(),
	})
}

// wrapCtor rewrites a constructor in function-value position to a closure
// (user decision: auto-wrap rather than error).
func (r *fileResolver) wrapCtor(use *ctorUse, targs []string, sig *types.Signature) {
	v := use.variant
	if sig.Params().Len() != len(v.Params) || sig.Variadic() {
		r.errorf(use.name.Pos(), "constructor %s takes %d arguments but a %d-parameter function is expected here",
			v.Name, len(v.Params), sig.Params().Len())
		return
	}
	litType, ok := r.ctorTypeText(use, targs)
	if !ok {
		return
	}
	resText, terr := r.typeText(sig.Results().At(0).Type())
	if terr != nil {
		r.errorf(use.name.Pos(), "%v", terr)
		return
	}
	var params, fields []string
	for i := 0; i < sig.Params().Len(); i++ {
		pt, terr := r.typeText(sig.Params().At(i).Type())
		if terr != nil {
			r.errorf(use.name.Pos(), "%v", terr)
			return
		}
		pname := fmt.Sprintf("p%d", i)
		params = append(params, pname+" "+pt)
		fields = append(fields, v.Params[i].FieldName+": "+pname)
	}
	out := use.outermost()
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(out.Pos()),
		End:   r.off(out.End()),
		New: fmt.Sprintf("func(%s) %s { return %s{%s} }",
			strings.Join(params, ", "), resText, litType, strings.Join(fields, ", ")),
	})
}

// ctorTypeText renders the variant struct type, instantiated with the
// kept subset of the enum's type arguments.
func (r *fileResolver) ctorTypeText(use *ctorUse, targs []string) (string, bool) {
	name := use.variant.TypeName
	if use.pkgAlias != "" {
		name = use.pkgAlias + "." + name
	} else if use.enum.PkgPath != r.pkg.PkgPath {
		alias, ok := r.importName(use.enum.PkgPath)
		if !ok {
			r.errorf(use.name.Pos(), "using constructor %s requires importing %q", use.variant.Name, use.enum.PkgPath)
			return "", false
		}
		name = alias + "." + name
	}
	kept := keptIndices(use.enum, use.variant)
	if len(kept) == 0 {
		return name, true
	}
	parts := make([]string, len(kept))
	for i, ki := range kept {
		parts[i] = targs[ki]
	}
	return name + "[" + strings.Join(parts, ", ") + "]", true
}

// keptIndices lists the enum type parameters a variant's struct keeps
// (GADT result refinement fixes the others).
func keptIndices(e *registry.Enum, v *registry.EnumVariant) []int {
	if v.ResultArgs == nil {
		out := make([]int, len(e.TParams))
		for i := range out {
			out[i] = i
		}
		return out
	}
	var out []int
	for i, arg := range v.ResultArgs {
		if i < len(e.TParams) && arg == e.TParams[i] {
			out = append(out, i)
		}
	}
	return out
}

func keptSet(e *registry.Enum, v *registry.EnumVariant) map[int]bool {
	out := map[int]bool{}
	for _, i := range keptIndices(e, v) {
		out[i] = true
	}
	return out
}

// explicitTargs maps explicit instantiation texts onto the enum's type
// parameters (explicit args instantiate the kept set).
func (r *fileResolver) explicitTargs(use *ctorUse) ([]string, bool) {
	kept := keptIndices(use.enum, use.variant)
	if len(use.explicit) != len(kept) {
		r.errorf(use.name.Pos(), "constructor %s takes %d type arguments, got %d",
			use.variant.Name, len(kept), len(use.explicit))
		return nil, false
	}
	targs := make([]string, len(use.enum.TParams))
	if use.variant.ResultArgs != nil {
		for i, arg := range use.variant.ResultArgs {
			targs[i] = arg
		}
	}
	for i, ki := range kept {
		targs[ki] = r.text(use.explicit[i].Pos(), use.explicit[i].End())
	}
	return targs, true
}

// targsFromExpected fills targs from a context-expected type that is this
// enum, this variant's struct, or a function returning either.
func (r *fileResolver) targsFromExpected(use *ctorUse, targs []string) ([]string, bool) {
	expected := r.expectedType(use.outermost())
	if expected == nil {
		return nil, false
	}
	if sig, ok := types.Unalias(expected).(*types.Signature); ok && sig.Results().Len() == 1 {
		expected = sig.Results().At(0).Type()
	}
	named, _ := asNamed(expected)
	if named == nil || named.Obj().Pkg() == nil || named.Obj().Pkg().Path() != use.enum.PkgPath {
		return nil, false
	}
	out := append([]string{}, targs...)
	fill := func(indices []int, ta *types.TypeList) bool {
		n := 0
		if ta != nil {
			n = ta.Len()
		}
		if n != len(indices) {
			return false
		}
		for i, idx := range indices {
			text, err := r.typeText(ta.At(i))
			if err != nil {
				return false
			}
			out[idx] = text
		}
		return true
	}
	switch named.Obj().Name() {
	case use.enum.Name:
		all := make([]int, len(use.enum.TParams))
		for i := range all {
			all[i] = i
		}
		if len(all) > 0 && !fill(all, named.TypeArgs()) {
			return nil, false
		}
	case use.variant.TypeName:
		kept := keptIndices(use.enum, use.variant)
		if len(kept) > 0 && !fill(kept, named.TypeArgs()) {
			return nil, false
		}
	default:
		return nil, false
	}
	for _, t := range out {
		if t == "" {
			return nil, false
		}
	}
	return out, true
}

// targsFromArgs unifies declared parameter types against evaluated
// argument types.
func (r *fileResolver) targsFromArgs(use *ctorUse, targs []string) ([]string, bool) {
	e, v := use.enum, use.variant
	if len(use.call.Args) != len(v.Params) {
		return nil, false
	}
	tparamIndex := map[string]int{}
	for i, n := range e.TParams {
		tparamIndex[n] = i
	}
	bound := make([]types.Type, len(e.TParams))
	for i, p := range v.Params {
		declExpr, err := parser.ParseExpr(p.Type)
		if err != nil {
			continue
		}
		argText := r.text(use.call.Args[i].Pos(), use.call.Args[i].End())
		tv, err := types.Eval(r.pkg.Fset, r.pkg.Types, use.call.Pos(), argText)
		if err != nil || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
			continue
		}
		if !unifyDecl(declExpr, types.Default(tv.Type), tparamIndex, bound) {
			return nil, false
		}
	}
	out := append([]string{}, targs...)
	for i := range out {
		if out[i] != "" {
			continue
		}
		if bound[i] == nil {
			return nil, false
		}
		text, err := r.typeText(bound[i])
		if err != nil {
			return nil, false
		}
		out[i] = text
	}
	return out, true
}

// unifyDecl structurally unifies a declared parameter type expression
// (in enum-tparam terms) against an actual argument type, binding tparams.
// Unknown shapes succeed without binding (the backstop judges them).
func unifyDecl(decl ast.Expr, actual types.Type, tparams map[string]int, bound []types.Type) bool {
	actual = types.Unalias(actual)
	switch d := decl.(type) {
	case *ast.ParenExpr:
		return unifyDecl(d.X, actual, tparams, bound)
	case *ast.Ident:
		i, isTParam := tparams[d.Name]
		if !isTParam {
			return true
		}
		if bound[i] == nil {
			bound[i] = actual
			return true
		}
		return types.Identical(bound[i], actual)
	case *ast.StarExpr:
		if p, ok := actual.(*types.Pointer); ok {
			return unifyDecl(d.X, p.Elem(), tparams, bound)
		}
		return false
	case *ast.ArrayType:
		if d.Len == nil {
			if s, ok := actual.(*types.Slice); ok {
				return unifyDecl(d.Elt, s.Elem(), tparams, bound)
			}
			return false
		}
		if a, ok := actual.(*types.Array); ok {
			return unifyDecl(d.Elt, a.Elem(), tparams, bound)
		}
		return false
	case *ast.MapType:
		if m, ok := actual.(*types.Map); ok {
			return unifyDecl(d.Key, m.Key(), tparams, bound) &&
				unifyDecl(d.Value, m.Elem(), tparams, bound)
		}
		return false
	case *ast.ChanType:
		if c, ok := actual.(*types.Chan); ok {
			return unifyDecl(d.Value, c.Elem(), tparams, bound)
		}
		return false
	case *ast.FuncType:
		sig, ok := actual.(*types.Signature)
		if !ok {
			return false
		}
		params := flattenFieldTypes(d.Params)
		results := flattenFieldTypes(d.Results)
		if len(params) != sig.Params().Len() || len(results) != sig.Results().Len() {
			return false
		}
		for i, p := range params {
			if !unifyDecl(p, sig.Params().At(i).Type(), tparams, bound) {
				return false
			}
		}
		for i, res := range results {
			if !unifyDecl(res, sig.Results().At(i).Type(), tparams, bound) {
				return false
			}
		}
		return true
	case *ast.IndexExpr:
		return unifyInstantiated(d.X, []ast.Expr{d.Index}, actual, tparams, bound)
	case *ast.IndexListExpr:
		return unifyInstantiated(d.X, d.Indices, actual, tparams, bound)
	}
	return true
}

func unifyInstantiated(base ast.Expr, args []ast.Expr, actual types.Type, tparams map[string]int, bound []types.Type) bool {
	named, _ := actual.(*types.Named)
	if named == nil || named.TypeArgs() == nil || named.TypeArgs().Len() != len(args) {
		return true // shape unknown; let the backstop judge
	}
	if id, ok := base.(*ast.Ident); ok && named.Obj().Name() != id.Name {
		return true
	}
	for i, a := range args {
		if !unifyDecl(a, named.TypeArgs().At(i), tparams, bound) {
			return false
		}
	}
	return true
}

func flattenFieldTypes(fl *ast.FieldList) []ast.Expr {
	if fl == nil {
		return nil
	}
	var out []ast.Expr
	for _, f := range fl.List {
		n := len(f.Names)
		if n == 0 {
			n = 1
		}
		for i := 0; i < n; i++ {
			out = append(out, f.Type)
		}
	}
	return out
}

// expectedFuncSig returns the expected function signature when this use
// sits where a function value producing this enum is expected.
func (r *fileResolver) expectedFuncSig(use *ctorUse) *types.Signature {
	expected := r.expectedType(use.outermost())
	if expected == nil {
		return nil
	}
	sig, ok := types.Unalias(expected).(*types.Signature)
	if !ok || sig.Results().Len() != 1 {
		return nil
	}
	named, _ := asNamed(sig.Results().At(0).Type())
	if named == nil || named.Obj().Pkg() == nil || named.Obj().Pkg().Path() != use.enum.PkgPath {
		return nil
	}
	if n := named.Obj().Name(); n != use.enum.Name && n != use.variant.TypeName {
		return nil
	}
	return sig
}

// expectedType walks up from e for the type the context expects.
func (r *fileResolver) expectedType(e ast.Expr) types.Type {
	info := r.pkg.TypesInfo
	switch p := r.parents[e].(type) {
	case *ast.ParenExpr:
		return r.expectedType(p)
	case *ast.AssignStmt:
		if p.Tok != token.ASSIGN {
			return nil // := infers FROM the rhs; nothing to propagate
		}
		for i, rhs := range p.Rhs {
			if rhs == e && i < len(p.Lhs) {
				if tv, ok := info.Types[p.Lhs[i]]; ok {
					return tv.Type
				}
			}
		}
	case *ast.ValueSpec:
		if p.Type == nil {
			return nil
		}
		if tv, ok := info.Types[p.Type]; ok && tv.IsType() {
			return tv.Type
		}
	case *ast.ReturnStmt:
		results := r.enclosingResults(p)
		for i, res := range p.Results {
			if res == e && i < len(results) {
				return results[i]
			}
		}
	case *ast.CallExpr:
		if p.Fun == e {
			return nil
		}
		tv, ok := info.Types[p.Fun]
		if !ok {
			return nil
		}
		sig, ok := types.Unalias(tv.Type).(*types.Signature)
		if !ok {
			return nil
		}
		for i, arg := range p.Args {
			if arg != e {
				continue
			}
			if sig.Variadic() && i >= sig.Params().Len()-1 && !p.Ellipsis.IsValid() {
				if s, ok := sig.Params().At(sig.Params().Len() - 1).Type().(*types.Slice); ok {
					return s.Elem()
				}
				return nil
			}
			if i < sig.Params().Len() {
				return sig.Params().At(i).Type()
			}
		}
	case *ast.KeyValueExpr:
		if p.Value == e {
			return r.compositeElemType(p, e)
		}
	case *ast.CompositeLit:
		return r.compositeElemType(p, e)
	case *ast.BinaryExpr:
		// A typed other operand: o == None.
		other := p.X
		if other == e {
			other = p.Y
		}
		if tv, ok := info.Types[other]; ok && tv.Type != nil && tv.Type != types.Typ[types.Invalid] {
			return tv.Type
		}
	case *ast.UnaryExpr:
		return nil
	}
	return nil
}

// compositeElemType finds the type a composite-literal element position
// expects (slice/array/map elements and struct fields).
func (r *fileResolver) compositeElemType(node ast.Node, e ast.Expr) types.Type {
	info := r.pkg.TypesInfo
	var lit *ast.CompositeLit
	var key ast.Expr
	switch n := node.(type) {
	case *ast.CompositeLit:
		lit = n
	case *ast.KeyValueExpr:
		key = n.Key
		l, ok := r.parents[n].(*ast.CompositeLit)
		if !ok {
			return nil
		}
		lit = l
	}
	tv, ok := info.Types[lit]
	if !ok || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
		if lit.Type == nil {
			return nil
		}
		ltv, lok := info.Types[lit.Type]
		if !lok || !ltv.IsType() {
			return nil
		}
		tv = ltv
	}
	t := types.Unalias(tv.Type)
	if named, isNamed := t.(*types.Named); isNamed {
		t = named.Underlying()
	}
	switch u := t.(type) {
	case *types.Slice:
		return u.Elem()
	case *types.Array:
		return u.Elem()
	case *types.Map:
		if key != nil && key != e {
			return u.Elem()
		}
		if key == e {
			return u.Key()
		}
		return u.Elem()
	case *types.Struct:
		if keyID, ok := key.(*ast.Ident); ok {
			for i := 0; i < u.NumFields(); i++ {
				if u.Field(i).Name() == keyID.Name {
					return u.Field(i).Type()
				}
			}
			return nil
		}
		for i, elt := range lit.Elts {
			if elt == e && i < u.NumFields() {
				return u.Field(i).Type()
			}
		}
	}
	return nil
}

// enclosingResults returns the result types of the function enclosing a
// return statement.
func (r *fileResolver) enclosingResults(ret *ast.ReturnStmt) []types.Type {
	info := r.pkg.TypesInfo
	var node ast.Node = ret
	for node != nil {
		node = r.parents[node]
		var ftype *ast.FuncType
		switch fn := node.(type) {
		case *ast.FuncDecl:
			ftype = fn.Type
		case *ast.FuncLit:
			ftype = fn.Type
		default:
			continue
		}
		if ftype.Results == nil {
			return nil
		}
		var out []types.Type
		for _, field := range ftype.Results.List {
			tv, ok := info.Types[field.Type]
			if !ok || !tv.IsType() {
				return nil
			}
			n := len(field.Names)
			if n == 0 {
				n = 1
			}
			for i := 0; i < n; i++ {
				out = append(out, tv.Type)
			}
		}
		return out
	}
	return nil
}

// ctorGiveUp reports the audit-pass diagnostic for an unresolvable use.
func (r *fileResolver) ctorGiveUp(use *ctorUse) {
	v := use.variant
	kept := keptIndices(use.enum, use.variant)
	if len(kept) == 0 && len(use.enum.TParams) == 0 {
		r.errorf(use.name.Pos(), "cannot resolve constructor %s here", v.Name)
		return
	}
	r.errorf(use.name.Pos(), "cannot infer the type arguments of constructor %s; write %s[...] or qualify with the enum type: %s[...].%s",
		v.Name, v.Name, use.enum.Name, v.Name)
}
