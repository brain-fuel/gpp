package resolve

import (
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"math/big"
	"strings"

	"goforge.dev/goplus/internal/core"
	"goforge.dev/goplus/internal/lower"
	"goforge.dev/goplus/internal/registry"
)

type dependentValueType struct {
	pkgPath  string
	typeText string
	origin   *ast.CallExpr
}

// indexDependentVariables retains dependent result types for locals after
// ordinary go/types has seen only their erased representation.
func (r *fileResolver) indexDependentVariables() {
	r.dependentVars = map[*types.Var]dependentValueType{}
	r.dependentUnstable = map[*types.Var]bool{}
	assignments := map[*types.Var]int{}
	objectOf := func(lhs ast.Expr) *types.Var {
		id, ok := lhs.(*ast.Ident)
		if !ok {
			return nil
		}
		obj, _ := r.pkg.TypesInfo.ObjectOf(id).(*types.Var)
		return obj
	}
	// Count first so the ordered recovery pass never trusts a value which is
	// reassigned later in the function.
	ast.Inspect(r.file, func(node ast.Node) bool {
		switch statement := node.(type) {
		case *ast.AssignStmt:
			for _, lhs := range statement.Lhs {
				if object := objectOf(lhs); object != nil {
					assignments[object]++
				}
			}
		case *ast.ValueSpec:
			for _, name := range statement.Names {
				if object := objectOf(name); object != nil {
					assignments[object]++
				}
			}
		}
		return true
	})
	for object, count := range assignments {
		if count != 1 {
			r.dependentUnstable[object] = true
		}
	}
	record := func(lhs ast.Expr, rhs ast.Expr) {
		obj := objectOf(lhs)
		if obj == nil || assignments[obj] != 1 {
			return
		}
		call, ok := rhs.(*ast.CallExpr)
		if !ok {
			return
		}
		pkgPath, typeText, ok := r.dependentCallResult(call)
		if ok {
			r.dependentVars[obj] = dependentValueType{pkgPath: pkgPath, typeText: typeText, origin: call}
		}
	}
	ast.Inspect(r.file, func(node ast.Node) bool {
		switch statement := node.(type) {
		case *ast.AssignStmt:
			if len(statement.Lhs) == len(statement.Rhs) {
				for i := range statement.Lhs {
					record(statement.Lhs[i], statement.Rhs[i])
				}
			}
		case *ast.ValueSpec:
			if len(statement.Names) == len(statement.Values) {
				for i := range statement.Names {
					record(statement.Names[i], statement.Values[i])
				}
			}
		}
		return true
	})
	// go/types sees only erased representations, so it cannot reject an
	// explicitly annotated dependent binding whose result index differs. Audit
	// those declarations while both the authored type and call witness remain.
	ast.Inspect(r.file, func(node ast.Node) bool {
		spec, ok := node.(*ast.ValueSpec)
		if !ok || spec.Type == nil || len(spec.Names) != len(spec.Values) {
			return true
		}
		expected := r.text(spec.Type.Pos(), spec.Type.End())
		for index, value := range spec.Values {
			call, ok := value.(*ast.CallExpr)
			if !ok {
				continue
			}
			_, actual, found := r.dependentCallResult(call)
			if !found || dependentTypeTextsEqual(expected, actual, r.reg.TotalDefs()) {
				continue
			}
			r.errorf(value.Pos(), "dependent index mismatch in binding %s: declared %s, got %s", spec.Names[index].Name, expected, actual)
		}
		return true
	})
}

func (r *fileResolver) dependentCallResult(call *ast.CallExpr) (string, string, bool) {
	fn, _, pkgPath := calleeIdent(r, call.Fun)
	if fn == nil {
		return "", "", false
	}
	d, ok := r.reg.LookupDepFn(pkgPath, fn.Name)
	if !ok {
		return r.dependentConstructorResult(call)
	}
	d = r.expandVariadicDependentCall(call, d)
	aligned, full, ok := alignDependentCallArgs(call.Args, d)
	if !ok || d.Result == "" {
		return "", "", false
	}
	_ = full
	sub := map[string]string{}
	for i, p := range d.Params {
		if aligned[i] != nil {
			value := r.text(aligned[i].Pos(), aligned[i].End())
			if p.Quantity == "0" {
				value = r.normalizeIndexText(value)
			}
			sub[p.Name] = value
		}
	}
	// Infer omitted index parameters from an indexed runtime argument. This is
	// the common preservation shape: Header(1 request Request[m,...]) returns
	// Request[m,...], while m itself is erased and omitted at the call site.
	if !full {
		variables := map[string]bool{}
		for _, p := range d.Params {
			// Quantity-zero parameters are the erased evidence/index variables
			// available for result refinement. This includes user-defined index
			// domains (for example a recursive type-level list), not only nat.
			if p.Quantity == "0" {
				variables[p.Name] = true
			}
		}
		for i, p := range d.Params {
			if aligned[i] == nil {
				continue
			}
			var actual string
			switch argument := aligned[i].(type) {
			case *ast.CallExpr:
				_, actual, _ = r.dependentCallResult(argument)
			case *ast.CompositeLit:
				_, actual, _ = r.dependentCompositeResult(argument)
			case *ast.Ident:
				if known, found := r.dependentIdentType(argument); found {
					actual = known.typeText
					// A prior indexing pass may have recorded this local before
					// its own omitted domain indices were inferred. Re-evaluate
					// the immutable producer so nested smart constructors refine
					// recursive index lists all the way to their ground tail.
					if known.origin != nil && known.origin != call {
						if _, refined, ok := r.dependentCallResult(known.origin); ok {
							actual = refined
						}
					}
				}
			}
			if actual != "" {
				unifyDependentInstantiation(p.Type, actual, variables, sub)
			}
		}
	}
	result, err := substTypeTextLite(d.Result, sub)
	if err != nil {
		return "", "", false
	}
	// The function's package and its result type's package need not be the
	// same (a local wrapper can return validate.Rule[T, p]). go/types still
	// retains the named package after dependent indices are erased, so prefer
	// that authoritative package when it is available.
	resultPkg := pkgPath
	if named, _ := asNamed(r.pkg.TypesInfo.TypeOf(call)); named != nil && named.Obj().Pkg() != nil {
		resultPkg = named.Obj().Pkg().Path()
	}
	return resultPkg, result, true
}

// dependentConstructorResult recovers the indexed result of a GADT variant
// constructor before constructor lowering erases it to a Go struct literal.
// This lets equal-shape consumers reject, for example, Vec[2] zipped with
// Vec[1], even when both values were just bound to local variables.
func (r *fileResolver) dependentConstructorResult(call *ast.CallExpr) (string, string, bool) {
	name := call.Fun
	switch instantiated := name.(type) {
	case *ast.IndexExpr:
		name = instantiated.X
	case *ast.IndexListExpr:
		name = instantiated.X
	}
	uses := r.recognizeCtors(name)
	if len(uses) == 0 {
		fn, selector, pkgPath := calleeIdent(r, call.Fun)
		if fn != nil {
			for _, enum := range r.reg.EnumsByVariantName(pkgPath, fn.Name) {
				variant, found := enum.Variant(fn.Name)
				if !found {
					continue
				}
				use := &ctorUse{enum: enum, variant: variant, name: name, full: call.Fun, call: call}
				if selector != nil {
					if alias, ok := selector.X.(*ast.Ident); ok {
						use.pkgAlias = alias.Name
					}
				}
				switch instantiated := call.Fun.(type) {
				case *ast.IndexExpr:
					use.explicit = []ast.Expr{instantiated.Index}
				case *ast.IndexListExpr:
					use.explicit = instantiated.Indices
				}
				uses = append(uses, use)
			}
		}
	}
	for _, use := range uses {
		if use.call != call || len(use.enum.Indices) == 0 {
			continue
		}
		targs, ok := r.inferTargs(use)
		if !ok || len(targs) != len(use.enum.TParams) {
			continue
		}
		bind := map[string]string{}
		variables := map[string]bool{}
		for i, parameter := range use.enum.TParams {
			bind[parameter] = targs[i]
			variables[parameter] = true
		}
		for _, index := range use.enum.Indices {
			variables[index.Name] = true
		}
		for i, parameter := range use.variant.Params {
			if i >= len(call.Args) {
				break
			}
			actual := ""
			switch argument := call.Args[i].(type) {
			case *ast.CallExpr:
				_, actual, _ = r.dependentCallResult(argument)
			case *ast.CompositeLit:
				_, actual, _ = r.dependentCompositeResult(argument)
			case *ast.Ident:
				if known, found := r.dependentIdentType(argument); found {
					actual = known.typeText
				}
			}
			if actual != "" {
				unifyDependentInstantiation(parameter.RawType, actual, variables, bind)
			}
		}
		resultArgs := make([]string, len(use.enum.TParams)+len(use.enum.Indices))
		indexAt := map[int]string{}
		for i, index := range use.enum.Indices {
			term := index.Name
			if i < len(use.variant.IndexArgs) {
				term = use.variant.IndexArgs[i]
			}
			indexAt[index.Pos] = term
		}
		typePosition := 0
		for position := range resultArgs {
			if term, indexed := indexAt[position]; indexed {
				resultArgs[position] = term
				continue
			}
			term := use.enum.TParams[typePosition]
			if typePosition < len(use.variant.ResultArgs) {
				term = use.variant.ResultArgs[typePosition]
			}
			resultArgs[position] = term
			typePosition++
		}
		resolved := make([]string, len(resultArgs))
		for i, argument := range resultArgs {
			resolved[i], _ = substTypeTextLite(argument, bind)
		}
		return use.enum.PkgPath, use.enum.Name + "[" + strings.Join(resolved, ", ") + "]", true
	}
	return "", "", false
}

func unifyDependentInstantiation(pattern, actual string, variables map[string]bool, bind map[string]string) bool {
	patternBase, patternArgs := instantiationBase(pattern)
	actualBase, actualArgs := instantiationBase(actual)
	if patternBase == "" || patternBase != actualBase || len(patternArgs) != len(actualArgs) {
		return false
	}
	for i := range patternArgs {
		if !unifyText(patternArgs[i], actualArgs[i], variables, bind) {
			return false
		}
	}
	return true
}

// normalizeIndexText canonicalizes authored index values to marker syntax.
// In source a nullary enum value is called as End(), while dependent type
// arguments spell the same tag as End. Structured recursive domains may nest
// both forms, so normalize through the first-order core before substitution.
func (r *fileResolver) normalizeIndexText(text string) string {
	term, err := core.ParseIndexTerm(text, nil)
	if err != nil {
		return text
	}
	term = core.ResolveTags(term, func(name string) (string, bool) {
		for _, enum := range r.reg.AllEnums() {
			if !enum.IsDomain {
				continue
			}
			for _, variant := range enum.Variants {
				if variant.Name == name {
					return enum.Name, true
				}
			}
		}
		return "", false
	})
	return term.String()
}

func (r *fileResolver) dependentIdentType(id *ast.Ident) (dependentValueType, bool) {
	obj, _ := r.pkg.TypesInfo.ObjectOf(id).(*types.Var)
	if obj == nil {
		return dependentValueType{}, false
	}
	if known, ok := r.dependentVars[obj]; ok {
		return known, true
	}

	var enclosing *ast.FuncDecl
	for _, declaration := range r.file.Decls {
		fn, ok := declaration.(*ast.FuncDecl)
		if ok && fn.Pos() <= id.Pos() && id.Pos() < fn.End() {
			enclosing = fn
			break
		}
	}
	if enclosing == nil {
		return dependentValueType{}, false
	}
	d, ok := r.reg.LookupDepFn(r.pkg.PkgPath, enclosing.Name.Name)
	if !ok {
		return dependentValueType{}, false
	}
	for _, parameter := range d.Params {
		if parameter.Name != id.Name {
			continue
		}
		base, _ := instantiationBase(parameter.Type)
		if base == "" {
			return dependentValueType{}, false
		}
		pkgPath := r.pkg.PkgPath
		if named, _ := asNamed(obj.Type()); named != nil && named.Obj().Pkg() != nil {
			pkgPath = named.Obj().Pkg().Path()
		}
		return dependentValueType{pkgPath: pkgPath, typeText: parameter.Type}, true
	}
	return dependentValueType{}, false
}

// dependentCompositeResult recovers a fixed-index GADT constructor after an
// earlier fixpoint iteration has lowered Constructor() to Variant{}. This is
// essential for nested dependent smart constructors: their runtime argument
// remains, but the producer call no longer does.
func (r *fileResolver) dependentCompositeResult(literal *ast.CompositeLit) (string, string, bool) {
	named, _ := asNamed(r.pkg.TypesInfo.TypeOf(literal))
	if named == nil || named.Obj() == nil || named.Obj().Pkg() == nil {
		return "", "", false
	}
	pkgPath := named.Obj().Pkg().Path()
	variantType := named.Obj().Name()
	for _, enum := range r.reg.AllEnums() {
		if enum.PkgPath != pkgPath || len(enum.TParams) != 0 || len(enum.Indices) == 0 {
			continue
		}
		for _, variant := range enum.Variants {
			if variant.TypeName != variantType || len(variant.IndexArgs) != len(enum.Indices) {
				continue
			}
			// Only recover indices fixed by the constructor itself. A generic
			// variant such as Tick(prev Counter[n]) still needs call-site
			// inference to instantiate n; returning its raw marker expression
			// here would turn Counter[2] into the spurious Counter[n+1].
			fixed := true
			for _, argument := range variant.IndexArgs {
				for _, binder := range enum.Indices {
					if indexTextUsesName(argument, binder.Name) {
						fixed = false
						break
					}
				}
				if !fixed {
					break
				}
			}
			if !fixed {
				continue
			}
			ordered := make([]string, len(enum.Indices))
			for index, binder := range enum.Indices {
				if binder.Pos < 0 || binder.Pos >= len(ordered) {
					return "", "", false
				}
				ordered[binder.Pos] = variant.IndexArgs[index]
			}
			return enum.PkgPath, enum.Name + "[" + strings.Join(ordered, ", ") + "]", true
		}
	}
	return "", "", false
}

func indexTextUsesName(text, name string) bool {
	for start := 0; start < len(text); {
		for start < len(text) && !((text[start] >= 'A' && text[start] <= 'Z') || (text[start] >= 'a' && text[start] <= 'z') || text[start] == '_') {
			start++
		}
		end := start
		for end < len(text) && ((text[end] >= 'A' && text[end] <= 'Z') || (text[end] >= 'a' && text[end] <= 'z') || (text[end] >= '0' && text[end] <= '9') || text[end] == '_') {
			end++
		}
		if text[start:end] == name {
			return true
		}
		start = end
	}
	return false
}

// Dependent call sites (v0.7.0). The surface passes every argument —
// erased ones included (`Head(2, v)`); the signature dropped its
// 0-quantity parameters in pass 1, so the call drops the matching
// arguments here. Idempotent by arity: a call already at the erased
// arity is left alone. Erased arguments must be index expressions
// (pure); anything effectful is an error — its evaluation would vanish.

// alignDependentCallArgs maps surface arguments back to authored parameter
// positions. Go+ permits inferable quantity-0 indices to be omitted, so a call
// may already have erased arity even though it still needs dependent checking
// and quantity-1 wrapping.
func alignDependentCallArgs(args []ast.Expr, d *registry.DepFn) (aligned []ast.Expr, full bool, ok bool) {
	if len(args) == len(d.Params) {
		return append([]ast.Expr(nil), args...), true, true
	}
	if len(args) != len(d.Params)-len(d.Dropped) {
		return nil, false, false
	}
	dropped := map[int]bool{}
	for _, position := range d.Dropped {
		dropped[position] = true
	}
	aligned = make([]ast.Expr, len(d.Params))
	next := 0
	for position := range d.Params {
		if dropped[position] {
			continue
		}
		aligned[position] = args[next]
		next++
	}
	return aligned, false, true
}

// expandVariadicDependentCall gives each variadic runtime argument its own
// authored parameter slot. This lets the ordinary dependent checker infer and
// compare a shared index across calls such as And(a, b, c), while preserving
// the single marker representation `values ...BoolExpr[n]`.
func (r *fileResolver) expandVariadicDependentCall(call *ast.CallExpr, d *registry.DepFn) *registry.DepFn {
	if len(d.Params) == 0 || !strings.HasPrefix(strings.TrimSpace(d.Params[len(d.Params)-1].Type), "...") {
		return d
	}
	explicitDropped := true
	for _, position := range d.Dropped {
		if position >= len(call.Args) || !r.explicitNaturalArgument(call.Args[position]) {
			explicitDropped = false
			break
		}
	}
	runtimeCount := len(call.Args)
	if explicitDropped {
		runtimeCount -= len(d.Dropped)
	}
	fixedRuntime := len(d.Params) - 1 - len(d.Dropped)
	variadicCount := runtimeCount - fixedRuntime
	if variadicCount < 0 {
		return d
	}
	clone := *d
	clone.Params = append([]registry.DepParam(nil), d.Params[:len(d.Params)-1]...)
	last := d.Params[len(d.Params)-1]
	last.Type = strings.TrimPrefix(strings.TrimSpace(last.Type), "...")
	for i := 0; i < variadicCount; i++ {
		clone.Params = append(clone.Params, last)
	}
	clone.Dropped = append([]int(nil), d.Dropped...)
	return &clone
}

func (r *fileResolver) explicitNaturalArgument(argument ast.Expr) bool {
	typeOf := r.pkg.TypesInfo.TypeOf(argument)
	if typeOf == nil {
		return pureIndexArg(argument)
	}
	basic, ok := types.Unalias(typeOf).(*types.Basic)
	return ok && basic.Info()&types.IsInteger != 0
}

// depCallCandidate drops erased arguments from one call.
func (r *fileResolver) depCallCandidate(call *ast.CallExpr) {
	if r.dependentBlocked[call] {
		return
	}
	fnIdent, _, pkgPath := calleeIdent(r, call.Fun)
	if fnIdent == nil {
		return
	}
	d, ok := r.reg.LookupDepFn(pkgPath, fnIdent.Name)
	if !ok {
		return
	}
	d = r.expandVariadicDependentCall(call, d)
	aligned, full, shapeOK := alignDependentCallArgs(call.Args, d)
	if !shapeOK {
		return
	}
	hasLinear := false
	for _, p := range d.Params {
		if p.Quantity == "1" {
			hasLinear = true
		}
	}
	// An omitted quantity-0 argument has the same arity as an already-erased
	// call from a later fixpoint. Validate both shapes: indexed runtime
	// arguments still carry enough marker information to infer the witness,
	// and the !full branch below prevents a second erasure edit.
	if full {
		indicesArePure := true
		for _, position := range d.Dropped {
			if position < len(call.Args) && !pureIndexArg(call.Args[position]) {
				indicesArePure = false
			}
		}
		if indicesArePure && !r.validateDependentIndexedArgs(call, d, pkgPath, aligned) {
			return
		}
	} else if !r.validateDependentIndexedArgs(call, d, pkgPath, aligned) {
		return
	}
	if len(d.Dropped) == 0 && !hasLinear {
		return
	}
	// Linear positions: wrap the argument in the callee package's
	// use-once constructor (LinOf / pkg.LinOf), once.
	linOf := "LinOf"
	if pkgPath != r.pkg.PkgPath {
		if alias, found := importAliasFor(r.file, pkgPath); found {
			linOf = alias + ".LinOf"
		}
	}
	for i, a := range aligned {
		if a == nil || d.Params[i].Quantity != "1" || isLinOfCall(a) {
			continue
		}
		r.edits = append(r.edits,
			lower.Edit{Start: r.off(a.Pos()), End: r.off(a.Pos()), New: linOf + "("},
			lower.Edit{Start: r.off(a.End()), End: r.off(a.End()), New: ")"})
	}
	if len(d.Dropped) == 0 {
		return
	}
	if !full {
		return // erased parameters were inferred and are already absent
	}
	dropped := map[int]bool{}
	for _, i := range d.Dropped {
		dropped[i] = true
	}
	for i, a := range call.Args {
		if !dropped[i] {
			continue
		}
		if !pureIndexArg(a) {
			if r.report {
				r.errorf(a.Pos(), "the argument for erased parameter %s of %s must be an index expression (it is erased at runtime)",
					d.Params[i].Name, d.Name)
			}
			return
		}
	}
	// Proof parameters (Eq[a, b]) discharge by refl through the decider
	// BEFORE anything drops: an unprovable equality leaves the call
	// intact for the audit pass to report.
	for i, a := range call.Args {
		if !dropped[i] {
			continue
		}
		base, eqArgs := instantiationBase(d.Params[i].Type)
		if base != "Eq" || len(eqArgs) != 2 {
			continue
		}
		id, isIdent := a.(*ast.Ident)
		if !isIdent || id.Name != "refl" {
			if r.report {
				r.errorf(a.Pos(), "the proof argument for %s of %s must be refl in v0.7.0", d.Params[i].Name, d.Name)
			}
			return
		}
		resolveKey := fileCallResolver(r.pkg.PkgPath, r.file)
		// The proposition's terms are written in the CALLEE's scope:
		// bare total-function names resolve against its package.
		calleeResolve := func(fun ast.Expr) (string, bool) {
			if id, isID := fun.(*ast.Ident); isID {
				return pkgPath + "." + id.Name, true
			}
			return resolveKey(fun)
		}
		sub := map[string]core.Term{}
		for j, p := range d.Params {
			if j == i || j >= len(call.Args) {
				continue
			}
			argText := string(r.src[r.off(call.Args[j].Pos()):r.off(call.Args[j].End())])
			if t, err := core.ParseIndexTerm(argText, resolveKey); err == nil {
				sub[p.Name] = t
			}
		}
		ok, err := core.DecideEqTexts(eqArgs[0], eqArgs[1], sub, r.reg.TotalDefs(), calleeResolve)
		if err != nil || !ok {
			if r.report {
				r.errorf(a.Pos(), "cannot prove %s = %s at this call to %s; the arithmetic decider could not discharge refl (rephrase the indices or pass values that make the equality manifest)",
					substText(eqArgs[0], sub), substText(eqArgs[1], sub), d.Name)
			}
			return
		}
	}
	for i, a := range call.Args {
		if !dropped[i] {
			continue
		}
		if i+1 < len(call.Args) {
			r.edits = append(r.edits, lower.Edit{Start: r.off(a.Pos()), End: r.off(call.Args[i+1].Pos()), New: ""})
		} else if i > 0 && !dropped[i-1] {
			// Last argument: consume the preceding comma — unless the
			// previous argument's own edit already did.
			r.edits = append(r.edits, lower.Edit{Start: r.off(call.Args[i-1].End()), End: r.off(a.End()), New: ""})
		} else {
			r.edits = append(r.edits, lower.Edit{Start: r.off(a.Pos()), End: r.off(a.End()), New: ""})
		}
	}
}

// validateDependentIndexedArgs checks indices which ordinary go/types cannot
// see after erasure. In particular, a nested call returning Fixed[3] cannot be
// passed where Fixed[2] is required merely because both erase to Fixed.
//
// Call results, single-assignment locals, and dependent parameters recover
// their original signatures from markers. Reassigned indexed locals are
// rejected because an erased Go interface cannot carry a flow-insensitive
// static index safely.
func (r *fileResolver) validateDependentIndexedArgs(call *ast.CallExpr, d *registry.DepFn, pkgPath string, args []ast.Expr) bool {
	valid := true
	outer := map[string]string{}
	variables := map[string]bool{}
	for i, p := range d.Params {
		if i < len(args) && args[i] != nil {
			value := r.text(args[i].Pos(), args[i].End())
			if p.Quantity == "0" {
				value = r.normalizeIndexText(value)
			}
			outer[p.Name] = value
		}
		if p.Quantity == "0" {
			variables[p.Name] = true
		}
	}
	implicit := false
	for _, argument := range args {
		implicit = implicit || argument == nil
	}
	if implicit {
		// Recover omitted indices from indexed runtime arguments before
		// substituting expected types below.
		for i, p := range d.Params {
			if i >= len(args) || args[i] == nil {
				continue
			}
			var actual string
			switch argument := args[i].(type) {
			case *ast.CallExpr:
				_, actual, _ = r.dependentCallResult(argument)
			case *ast.CompositeLit:
				_, actual, _ = r.dependentCompositeResult(argument)
			case *ast.Ident:
				if known, found := r.dependentIdentType(argument); found {
					actual = known.typeText
				}
			}
			if actual != "" {
				unifyDependentInstantiation(p.Type, actual, variables, outer)
			}
		}
	}
	// A natural index can occur below an ordinary type parameter, for example
	// Term[UninterpretedSort[domain]]. The outer Term is not itself indexed,
	// so the direct index-position audit below cannot see this fact. Once the
	// omitted witnesses have been inferred, compare these nested dependent
	// instantiations structurally as well.
	for i, p := range d.Params {
		if i >= len(args) || args[i] == nil || !nestedDependentType(p.Type, variables) {
			continue
		}
		expected, err := substTypeTextLite(p.Type, outer)
		if err != nil {
			continue
		}
		actual := ""
		switch argument := args[i].(type) {
		case *ast.CallExpr:
			_, actual, _ = r.dependentCallResult(argument)
		case *ast.CompositeLit:
			_, actual, _ = r.dependentCompositeResult(argument)
		case *ast.Ident:
			if known, found := r.dependentIdentType(argument); found {
				actual = known.typeText
			}
		}
		if actual == "" || dependentTypeTextsEqual(expected, actual, r.reg.TotalDefs()) {
			continue
		}
		r.errorf(args[i].Pos(), "dependent index mismatch for argument %d to %s: requires %s, got %s", i+1, d.Name, expected, actual)
		valid = false
	}
	for i, p := range d.Params {
		if i >= len(args) {
			break
		}
		if args[i] == nil {
			continue
		}
		expectedRawBase, expectedRawArgs := instantiationBase(p.Type)
		expected, err := substTypeTextLite(p.Type, outer)
		if err != nil {
			continue
		}
		expectedBase, expectedArgs := instantiationBase(expected)
		if expectedBase == "" {
			continue
		}
		if expectedRawBase != expectedBase || len(expectedRawArgs) != len(expectedArgs) {
			continue
		}
		expectedPkg := instantiationPkgPath(p.Type, pkgPath, r.file)
		indexPositions := map[int]bool{}
		if enum, found := r.reg.LookupEnum(expectedPkg, expectedBase); found {
			for _, index := range enum.Indices {
				indexPositions[index.Pos] = true
			}
		}
		for pos, raw := range expectedRawArgs {
			for _, candidate := range d.Params {
				if candidate.Quantity == "0" && strings.TrimSpace(raw) == candidate.Name {
					indexPositions[pos] = true
				}
			}
		}
		if len(indexPositions) == 0 {
			continue
		}

		actualPkg, actual := "", ""
		var actualOrigin *ast.CallExpr
		actualKnown := true
		switch argument := args[i].(type) {
		case *ast.CallExpr:
			var found bool
			actualPkg, actual, found = r.dependentCallResult(argument)
			actualOrigin = argument
			if !found {
				continue
			}
		case *ast.CompositeLit:
			var found bool
			actualPkg, actual, found = r.dependentCompositeResult(argument)
			if !found {
				continue
			}
		case *ast.Ident:
			object, _ := r.pkg.TypesInfo.ObjectOf(argument).(*types.Var)
			if r.dependentUnstable[object] {
				r.errorf(argument.Pos(), "cannot establish the dependent index of reassigned value %s at this call to %s; bind each indexed value once or rescale explicitly", argument.Name, d.Name)
				valid = false
				continue
			}
			known, found := r.dependentIdentType(argument)
			if !found {
				actualKnown = false
				break
			}
			actualPkg, actual = known.pkgPath, known.typeText
			actualOrigin = known.origin
		default:
			actualKnown = false
		}
		if !actualKnown {
			continue
		}
		actualBase, actualArgs := instantiationBase(actual)
		// Ordinary go/types has already established assignability of the
		// erased named types. Do not require package recovery here: TypesInfo
		// can be incomplete while calls still contain their soon-to-be-erased
		// arguments, and marker results can be returned through local wrappers.
		// The registry lookup above identifies which argument positions are
		// indices; base name and arity are sufficient for comparing those facts.
		_ = actualPkg
		if actualBase != expectedBase || len(actualArgs) != len(expectedArgs) {
			continue
		}

		for pos := range indexPositions {
			if pos >= len(expectedArgs) || pos >= len(actualArgs) {
				continue
			}
			want, got := expectedArgs[pos], actualArgs[pos]
			equal, decideErr := core.DecideEqTexts(want, got, nil, r.reg.TotalDefs(), nil)
			if decideErr == nil && equal {
				continue
			}
			if actualOrigin != nil {
				variables := r.constructorIndexNames(actualOrigin)
				if unifyText(got, want, variables, map[string]string{}) {
					continue
				}
				if existentialEqual, supported := existsConstructorIndexEquality(want, got, variables); supported && existentialEqual {
					continue
				}
			}
			// An already-erased call encountered by a later fixpoint may no
			// longer retain enough origin information to solve an omitted
			// witness. Only diagnose concrete contradictions; an unresolved
			// callee variable is an inference give-up, not evidence of mismatch.
			unresolved := false
			for variable := range variables {
				if containsTypeIdentifier(want, variable) {
					unresolved = true
					break
				}
			}
			if unresolved {
				continue
			}
			// Both signatures and all substitutions are concrete marker facts;
			// unlike inference give-ups this mismatch cannot resolve in a later
			// fixpoint iteration. Report it before nested calls erase their args.
			r.errorf(args[i].Pos(), "dependent index mismatch for argument %d to %s: requires %s[%s], got %s[%s]", i+1, d.Name, expectedBase, want, actualBase, got)
			// Keep a mismatching nested producer unerased in this iteration.
			// Otherwise its index arguments disappear before the audit pass and
			// the enclosing mismatch can be lost at the next fixpoint.
			if nested, ok := args[i].(*ast.CallExpr); ok {
				r.dependentBlocked[nested] = true
			}
			if identifier, ok := args[i].(*ast.Ident); ok {
				if known, found := r.dependentIdentType(identifier); found && known.origin != nil {
					r.blockDependentOrigin(known.origin)
				}
			}
			valid = false
		}
	}
	return valid
}

func dependentTypeTextsEqual(left, right string, totals core.Defs) bool {
	leftBase, leftArguments := instantiationBase(left)
	rightBase, rightArguments := instantiationBase(right)
	if leftBase != "" || rightBase != "" {
		if leftBase == "" || leftBase != rightBase || len(leftArguments) != len(rightArguments) {
			return false
		}
		for index := range leftArguments {
			if !dependentTypeTextsEqual(leftArguments[index], rightArguments[index], totals) {
				return false
			}
		}
		return true
	}
	if equal, err := core.DecideEqTexts(left, right, nil, totals, nil); err == nil && equal {
		return true
	}
	return strings.TrimSpace(left) == strings.TrimSpace(right)
}

func nestedDependentType(typeText string, variables map[string]bool) bool {
	_, arguments := instantiationBase(typeText)
	for _, argument := range arguments {
		if nestedBase, _ := instantiationBase(argument); nestedBase == "" {
			continue
		}
		for variable := range variables {
			if containsTypeIdentifier(argument, variable) {
				return true
			}
		}
	}
	return false
}

func (r *fileResolver) blockDependentOrigin(origin *ast.CallExpr) {
	r.dependentBlocked[origin] = true
	start, end := r.off(origin.Pos()), r.off(origin.End())
	kept := r.edits[:0]
	for _, edit := range r.edits {
		if edit.Start >= start && edit.End <= end {
			continue
		}
		kept = append(kept, edit)
	}
	r.edits = kept
}

func (r *fileResolver) constructorIndexNames(call *ast.CallExpr) map[string]bool {
	fn, _, pkgPath := calleeIdent(r, call.Fun)
	if fn == nil {
		return nil
	}
	for _, enum := range r.reg.EnumsByVariantName(pkgPath, fn.Name) {
		if _, found := enum.Variant(fn.Name); !found {
			continue
		}
		out := map[string]bool{}
		for _, index := range enum.Indices {
			out[index.Name] = true
		}
		return out
	}
	return nil
}

type affineIndex struct {
	constant *big.Int
	coef     map[string]*big.Int
}

// existsConstructorIndexEquality solves the hidden natural introduced by a
// polymorphic indexed constructor. For example Succ(Zero()) has Fin[n+2]; it
// fits Fin[2] with n=0 but cannot fit Fin[1]. This is existential solving only
// for constructor-local binders, never for caller parameters (which remain
// universally quantified and continue through the ordinary equality decider).
func existsConstructorIndexEquality(want, got string, variables map[string]bool) (bool, bool) {
	if len(variables) == 0 {
		return false, false
	}
	wantExpr, wantErr := parser.ParseExpr(want)
	gotExpr, gotErr := parser.ParseExpr(got)
	if wantErr != nil || gotErr != nil {
		return false, false
	}
	w, ok := affineOf(wantExpr, variables)
	if !ok {
		return false, false
	}
	g, ok := affineOf(gotExpr, variables)
	if !ok {
		return false, false
	}
	diff := affineAdd(g, affineScale(w, big.NewInt(-1)))
	var coefficient *big.Int
	for _, value := range diff.coef {
		if value.Sign() == 0 {
			continue
		}
		if coefficient != nil {
			return false, false
		}
		coefficient = value
	}
	if coefficient == nil {
		return diff.constant.Sign() == 0, true
	}
	numerator := new(big.Int).Neg(diff.constant)
	quotient, remainder := new(big.Int), new(big.Int)
	quotient.QuoRem(numerator, coefficient, remainder)
	return remainder.Sign() == 0 && quotient.Sign() >= 0, true
}

func affineOf(expression ast.Expr, variables map[string]bool) (affineIndex, bool) {
	switch value := expression.(type) {
	case *ast.BasicLit:
		if value.Kind != token.INT {
			return affineIndex{}, false
		}
		number := new(big.Int)
		if _, ok := number.SetString(value.Value, 0); !ok {
			return affineIndex{}, false
		}
		return affineIndex{constant: number, coef: map[string]*big.Int{}}, true
	case *ast.Ident:
		if !variables[value.Name] {
			return affineIndex{}, false
		}
		return affineIndex{constant: new(big.Int), coef: map[string]*big.Int{value.Name: big.NewInt(1)}}, true
	case *ast.ParenExpr:
		return affineOf(value.X, variables)
	case *ast.BinaryExpr:
		left, leftOK := affineOf(value.X, variables)
		right, rightOK := affineOf(value.Y, variables)
		if !leftOK || !rightOK {
			return affineIndex{}, false
		}
		switch value.Op {
		case token.ADD:
			return affineAdd(left, right), true
		case token.SUB:
			return affineAdd(left, affineScale(right, big.NewInt(-1))), true
		case token.MUL:
			if len(left.coef) == 0 {
				return affineScale(right, left.constant), true
			}
			if len(right.coef) == 0 {
				return affineScale(left, right.constant), true
			}
		}
	}
	return affineIndex{}, false
}

func affineAdd(left, right affineIndex) affineIndex {
	out := affineIndex{constant: new(big.Int).Add(left.constant, right.constant), coef: map[string]*big.Int{}}
	for name, value := range left.coef {
		out.coef[name] = new(big.Int).Set(value)
	}
	for name, value := range right.coef {
		if previous := out.coef[name]; previous != nil {
			previous.Add(previous, value)
		} else {
			out.coef[name] = new(big.Int).Set(value)
		}
	}
	return out
}

func affineScale(value affineIndex, factor *big.Int) affineIndex {
	out := affineIndex{constant: new(big.Int).Mul(value.constant, factor), coef: map[string]*big.Int{}}
	for name, coefficient := range value.coef {
		out.coef[name] = new(big.Int).Mul(coefficient, factor)
	}
	return out
}

// instantiationPkgPath resolves the package which defines an instantiated
// type. Marker types belonging to the callee are normally bare; marker types
// on local wrappers may instead be qualified by one of the current file's
// imports (for example validate.Rule[T, p]).
func instantiationPkgPath(typeText, defaultPkg string, file *ast.File) string {
	open := strings.IndexByte(typeText, '[')
	if open <= 0 {
		return defaultPkg
	}
	base := strings.TrimSpace(typeText[:open])
	dot := strings.LastIndexByte(base, '.')
	if dot <= 0 {
		return defaultPkg
	}
	if path, found := fileImportPath(file, strings.TrimSpace(base[:dot])); found {
		return path
	}
	return defaultPkg
}

// pureIndexArg reports whether an expression is a pure index term:
// identifiers, literals, arithmetic, parens, and calls to totals
// (validated as total elsewhere; effectful calls are not total).
func pureIndexArg(e ast.Expr) bool {
	switch x := e.(type) {
	case *ast.Ident, *ast.BasicLit:
		return true
	case *ast.ParenExpr:
		return pureIndexArg(x.X)
	case *ast.BinaryExpr:
		return pureIndexArg(x.X) && pureIndexArg(x.Y)
	case *ast.SelectorExpr:
		return true
	case *ast.CallExpr:
		for _, a := range x.Args {
			if !pureIndexArg(a) {
				return false
			}
		}
		return pureIndexArg(x.Fun)
	}
	return false
}

// scrutineeIndexTerms recovers a match scrutinee's index terms when the
// scrutinee is a parameter of the enclosing dependent function — its
// //goplus:dep marker preserves the unerased type. Unknown otherwise
// (conservative: every variant stays possible).
func (r *fileResolver) scrutineeIndexTerms(e *registry.Enum, subj ast.Expr) []string {
	if len(e.Indices) == 0 {
		return nil
	}
	id, ok := subj.(*ast.Ident)
	if !ok {
		return nil
	}
	var encl *ast.FuncDecl
	for _, decl := range r.file.Decls {
		if fd, isFn := decl.(*ast.FuncDecl); isFn && fd.Pos() <= subj.Pos() && subj.Pos() < fd.End() {
			encl = fd
		}
	}
	if encl == nil {
		return nil
	}
	if enum, terms, found := r.reg.LookupParamIndex(r.pkg.PkgPath, encl.Name.Name, id.Name); found {
		if enum == e.Name && len(terms) == len(e.Indices) {
			return terms
		}
	}
	d, ok := r.reg.LookupDepFn(r.pkg.PkgPath, encl.Name.Name)
	if !ok {
		return nil
	}
	for _, p := range d.Params {
		if p.Name != id.Name {
			continue
		}
		base, args := instantiationBase(p.Type)
		if base != e.Name || len(args) != len(e.TParams)+len(e.Indices) {
			return nil
		}
		idxPos := map[int]bool{}
		for _, ib := range e.Indices {
			idxPos[ib.Pos] = true
		}
		var terms []string
		for i, a := range args {
			if idxPos[i] {
				terms = append(terms, a)
			}
		}
		return terms
	}
	return nil
}

// instantiationBase splits "Vec[T, n+1]" into base name and args.
func instantiationBase(text string) (string, []string) {
	open := strings.IndexByte(text, '[')
	if open <= 0 || !strings.HasSuffix(text, "]") {
		return "", nil
	}
	base := strings.TrimSpace(text[:open])
	if i := strings.LastIndexByte(base, '.'); i >= 0 {
		base = base[i+1:]
	}
	var args []string
	for _, part := range splitArgsTopLevel(text[open+1 : len(text)-1]) {
		args = append(args, strings.TrimSpace(part))
	}
	return base, args
}

// splitArgsTopLevel splits comma-separated args at bracket depth zero.
func splitArgsTopLevel(s string) []string {
	var out []string
	depth, start := 0, 0
	for i := 0; i < len(s); i++ {
		switch s[i] {
		case '[', '(':
			depth++
		case ']', ')':
			depth--
		case ',':
			if depth == 0 {
				out = append(out, s[start:i])
				start = i + 1
			}
		}
	}
	return append(out, s[start:])
}

// substText renders an index text after parameter substitution (for
// diagnostics; falls back to the raw text).
func substText(text string, sub map[string]core.Term) string {
	t, err := core.ParseIndexTerm(text, nil)
	if err != nil {
		return text
	}
	return core.SubstVars(t, sub).String()
}

// isLinOfCall reports whether an argument is already wrapped.
func isLinOfCall(e ast.Expr) bool {
	call, ok := e.(*ast.CallExpr)
	if !ok {
		return false
	}
	switch f := call.Fun.(type) {
	case *ast.Ident:
		return f.Name == "LinOf"
	case *ast.SelectorExpr:
		return f.Sel.Name == "LinOf"
	}
	return false
}

// importAliasFor finds the file's alias for an import path.
func importAliasFor(file *ast.File, path string) (string, bool) {
	for _, imp := range file.Imports {
		p := strings.Trim(imp.Path.Value, "\"")
		if p != path {
			continue
		}
		if imp.Name != nil {
			return imp.Name.Name, true
		}
		return p[strings.LastIndex(p, "/")+1:], true
	}
	return "", false
}

// fileCallResolver canonicalizes callee names against a file's imports
// (the marker-side twin lives in registry).
func fileCallResolver(pkgPath string, file *ast.File) core.CallResolver {
	return func(fun ast.Expr) (string, bool) {
		switch f := fun.(type) {
		case *ast.Ident:
			return pkgPath + "." + f.Name, true
		case *ast.SelectorExpr:
			alias, ok := f.X.(*ast.Ident)
			if !ok {
				return "", false
			}
			if path, found := fileImportPath(file, alias.Name); found {
				return path + "." + f.Sel.Name, true
			}
		}
		return "", false
	}
}
