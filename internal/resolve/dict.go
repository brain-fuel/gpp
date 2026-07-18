package resolve

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"strconv"
	"strings"

	"golang.org/x/tools/go/packages"

	"goforge.dev/gpp/internal/directive"
	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/registry"
)

// Dictionary passing (v0.5.0). A class constraint `[T Monoid]` on a
// function lowers to `[T any]` plus a leading witness value parameter;
// every call site receives the resolved instance implicitly. Recognition
// is purely syntactic and happens once in buildRegistry — before the
// first typecheck — so call sites anywhere see the dictionary shape from
// iteration 1.

// registerConstrainedFns walks the local shadow ASTs for function type
// parameters constrained by registered classes. Constraint shapes: a bare
// class name, an imported alias.Class, or an interface literal embedding
// only class names (multiple witnesses, in order).
func registerConstrainedFns(reg *registry.Registry, roots []*packages.Package, in *Input) {
	for _, pkg := range roots {
		for i, fileAST := range pkg.Syntax {
			if i >= len(pkg.CompiledGoFiles) {
				break
			}
			if _, ours := in.Texts[pkg.CompiledGoFiles[i]]; !ours {
				continue
			}
			for _, decl := range fileAST.Decls {
				fd, ok := decl.(*ast.FuncDecl)
				if !ok || fd.Recv != nil || fd.Type.TypeParams == nil {
					continue
				}
				fn := &registry.ConstrainedFn{PkgPath: pkg.PkgPath, Name: fd.Name.Name}
				for _, field := range fd.Type.TypeParams.List {
					refs := constraintClassRefs(reg, pkg.PkgPath, fileAST, field.Type)
					for _, ref := range refs {
						for _, n := range field.Names {
							fn.Dicts = append(fn.Dicts, registry.DictParam{TParam: n.Name, Class: ref})
						}
					}
				}
				if len(fn.Dicts) == 0 {
					continue
				}
				nameDictParams(fn, fd, pkg)
				reg.AddConstrainedFn(fn)
			}
		}
	}
}

// constraintClassRefs interprets one constraint expression as class refs.
// Returns nil when the constraint is ordinary Go (or mixed — the decl
// rewriter reports mixed literals).
func constraintClassRefs(reg *registry.Registry, pkgPath string, file *ast.File, expr ast.Expr) []registry.ClassRef {
	switch t := expr.(type) {
	case *ast.Ident:
		ref := registry.ClassRef{PkgPath: pkgPath, Name: t.Name}
		if _, ok := reg.LookupClass(ref); ok {
			return []registry.ClassRef{ref}
		}
	case *ast.SelectorExpr:
		alias, isID := t.X.(*ast.Ident)
		if !isID {
			return nil
		}
		if path, ok := fileImportPath(file, alias.Name); ok {
			ref := registry.ClassRef{PkgPath: path, Name: t.Sel.Name}
			if _, found := reg.LookupClass(ref); found {
				return []registry.ClassRef{ref}
			}
		}
	case *ast.InterfaceType:
		var refs []registry.ClassRef
		for _, m := range t.Methods.List {
			if len(m.Names) > 0 {
				return nil // method element: ordinary interface
			}
			sub := constraintClassRefs(reg, pkgPath, file, m.Type)
			if len(sub) != 1 {
				return nil // non-class element: ordinary (or mixed) constraint
			}
			refs = append(refs, sub[0])
		}
		if len(refs) == len(t.Methods.List) {
			return refs
		}
	}
	return nil
}

// fileImportPath resolves an import alias within one file.
func fileImportPath(file *ast.File, alias string) (string, bool) {
	for _, imp := range file.Imports {
		path, err := strconv.Unquote(imp.Path.Value)
		if err != nil {
			continue
		}
		name := ""
		if imp.Name != nil {
			name = imp.Name.Name
		} else if i := strings.LastIndex(path, "/"); i >= 0 {
			name = path[i+1:]
		} else {
			name = path
		}
		if name == alias {
			return path, true
		}
	}
	return "", false
}

// nameDictParams assigns deterministic dictionary parameter names:
// lowerCamel(class), then +TParam on collision, then numeric. Only
// identifiers that actually RESOLVE count as taken — an unresolved
// `monoid.Combine(…)` in the body is a deliberate forward reference to
// the parameter this function is about to gain.
func nameDictParams(fn *registry.ConstrainedFn, fd *ast.FuncDecl, pkg *packages.Package) {
	used := map[string]bool{}
	ast.Inspect(fd, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			if pkg.TypesInfo.Uses[id] != nil || pkg.TypesInfo.Defs[id] != nil {
				used[id.Name] = true
			}
		}
		return true
	})
	taken := map[string]bool{}
	for i := range fn.Dicts {
		base := lowerCamel(fn.Dicts[i].Class.Name)
		name := base
		if used[name] || taken[name] {
			name = base + fn.Dicts[i].TParam
		}
		for j := 1; used[name] || taken[name]; j++ {
			name = fmt.Sprintf("%s%d", base, j)
		}
		taken[name] = true
		fn.Dicts[i].ParamName = name
	}
}

func lowerCamel(s string) string {
	if s == "" {
		return s
	}
	return strings.ToLower(s[:1]) + s[1:]
}

// dictDeclCandidate rewrites a constrained function's declaration:
// constraint text → any, dictionary parameters prepended, //gpp:fn
// marker inserted. Idempotent: once the marker is present, skip.
func (r *fileResolver) dictDeclCandidate(fd *ast.FuncDecl) {
	if fd.Recv != nil || fd.Type.TypeParams == nil {
		return
	}
	fn, ok := r.reg.LookupConstrainedFn(r.pkg.PkgPath, fd.Name.Name)
	if !ok {
		return
	}
	if hasFnMarker(fd) {
		return // already rewritten
	}

	// Constraint spans → any (one edit per constrained tparam field).
	byTParam := map[string]*registry.DictParam{}
	for i := range fn.Dicts {
		byTParam[fn.Dicts[i].TParam] = &fn.Dicts[i]
	}
	var edits []lower.Edit
	rewrote := false
	for _, field := range fd.Type.TypeParams.List {
		hasDict := false
		for _, n := range field.Names {
			if byTParam[n.Name] != nil {
				hasDict = true
			}
		}
		if !hasDict {
			// Mixed class/interface literals never register; report them.
			if lit, isLit := field.Type.(*ast.InterfaceType); isLit && r.report {
				for _, m := range lit.Methods.List {
					if len(m.Names) > 0 {
						continue
					}
					if id, isID := m.Type.(*ast.Ident); isID && r.reg.HasClassName(id.Name) {
						r.errorf(field.Type.Pos(), "constraints may not mix classes and interfaces (v0.5.0); split %s out of the interface literal", id.Name)
						return
					}
				}
			}
			continue
		}
		edits = append(edits, lower.Edit{Start: r.off(field.Type.Pos()), End: r.off(field.Type.End()), New: "any"})
		rewrote = true
	}
	if !rewrote {
		return
	}

	// Dictionary parameters, in dict order, prepended.
	var params []string
	for _, d := range fn.Dicts {
		wt, ok := r.witnessTypeText(d.Class, d.TParam)
		if !ok {
			return
		}
		params = append(params, d.ParamName+" "+wt)
	}
	opening := r.off(fd.Type.Params.Opening) + 1
	sep := ", "
	if len(fd.Type.Params.List) == 0 {
		sep = ""
	}
	edits = append(edits, lower.Edit{Start: opening, End: opening, New: strings.Join(params, ", ") + sep})

	// //gpp:fn marker above the declaration.
	var constraints []string
	for _, d := range fn.Dicts {
		ref := d.Class
		if ref.PkgPath == r.pkg.PkgPath {
			constraints = append(constraints, d.TParam+" "+ref.Name)
		} else {
			constraints = append(constraints, d.TParam+" "+strconv.Quote(ref.PkgPath)+"."+ref.Name)
		}
	}
	marker := directive.FnMarker{Name: fd.Name.Name, Constraints: strings.Join(constraints, ", ")}
	at := r.off(fd.Pos())
	if fd.Doc != nil {
		at = r.off(fd.Doc.Pos())
	}
	for at > 0 && r.src[at-1] != '\n' {
		at--
	}
	edits = append(edits, lower.Edit{Start: at, End: at, New: marker.String() + "\n"})
	r.edits = append(r.edits, edits...)
}

// hasFnMarker reports whether the decl already carries //gpp:fn.
func hasFnMarker(fd *ast.FuncDecl) bool {
	if fd.Doc == nil {
		return false
	}
	for _, c := range fd.Doc.List {
		if _, ok := directive.ParseFnMarker(c.Text); ok {
			return true
		}
	}
	return false
}

// witnessTypeText renders a class's witness type applied to a tparam in
// this file's namespace.
func (r *fileResolver) witnessTypeText(ref registry.ClassRef, arg string) (string, bool) {
	if ref.PkgPath == r.pkg.PkgPath {
		return ref.Name + "[" + arg + "]", true
	}
	alias, ok := r.importName(ref.PkgPath)
	if !ok {
		r.errorf(token.NoPos, "using class %s requires importing %q", ref.Name, ref.PkgPath)
		return "", false
	}
	return alias + "." + ref.Name + "[" + arg + "]", true
}

// dictCallCandidate inserts dictionary arguments at a call of a
// constrained function.
func (r *fileResolver) dictCallCandidate(call *ast.CallExpr) {
	fnIdent, sel, pkgPath := calleeIdent(r, call.Fun)
	if fnIdent == nil || !r.reg.HasConstrainedFnName(fnIdent.Name) {
		return
	}
	fn, ok := r.reg.LookupConstrainedFn(pkgPath, fnIdent.Name)
	if !ok {
		return
	}
	// The callee must still lack its dictionaries. The escape hatch and
	// idempotence share one rule: a call whose leading arguments already
	// carry the witnesses — or whose arity says they were added — is left
	// alone (explicit passing IS calling the lowered signature).
	sig := r.constrainedSignature(fn)
	if sig == nil {
		if r.report {
			r.errorf(call.Pos(), "cannot resolve this call to %s: its lowered signature is unknown", fnIdent.Name)
		}
		return
	}
	origParams := sig.Params().Len() - len(fn.Dicts)
	if dictAlreadyPassed(r, call, fn, sig) {
		return
	}
	if !sig.Variadic() && len(call.Args) != origParams {
		return // explicit witnesses (or an arity error the backstop reports)
	}
	if sig.Variadic() && len(call.Args) >= origParams+len(fn.Dicts) {
		return
	}

	// Resolve each constrained tparam's type argument.
	targs, terr := r.typeArgsFor(call, fnIdent, sel, fn, sig)
	if terr != nil {
		if r.report {
			r.errorf(call.Pos(), "%v", terr)
		}
		return
	}
	if targs == nil {
		return // wait
	}

	var dictExprs []string
	for i, d := range fn.Dicts {
		expr, ok := r.dictExprFor(call, d, targs[i])
		if !ok {
			return
		}
		dictExprs = append(dictExprs, expr)
	}
	at := r.off(call.Lparen) + 1
	sep := ", "
	if len(call.Args) == 0 {
		sep = ""
	}
	r.edits = append(r.edits, lower.Edit{Start: at, End: at, New: strings.Join(dictExprs, ", ") + sep})
}

// calleeIdent digs the called function's identifier out of an
// (optionally instantiated, optionally qualified) callee expression.
func calleeIdent(r *fileResolver, fun ast.Expr) (id *ast.Ident, sel *ast.SelectorExpr, pkgPath string) {
	e := fun
	switch t := e.(type) {
	case *ast.IndexExpr:
		e = t.X
	case *ast.IndexListExpr:
		e = t.X
	}
	switch t := e.(type) {
	case *ast.Ident:
		return t, nil, r.pkg.PkgPath
	case *ast.SelectorExpr:
		alias, ok := t.X.(*ast.Ident)
		if !ok {
			return nil, nil, ""
		}
		if path, found := fileImportPath(r.file, alias.Name); found {
			return t.Sel, t, path
		}
	}
	return nil, nil, ""
}

// constrainedSignature reads the lowered (dict-taking) signature of a
// constrained function from the loaded types.
func (r *fileResolver) constrainedSignature(fn *registry.ConstrainedFn) *types.Signature {
	pkg := r.typesByPath[fn.PkgPath]
	if pkg == nil {
		return nil
	}
	obj := pkg.Scope().Lookup(fn.Name)
	if obj == nil {
		return nil
	}
	sig, _ := obj.Type().(*types.Signature)
	if sig == nil {
		return nil
	}
	if sig.Params().Len() < len(fn.Dicts) {
		return nil // decl not rewritten yet: wait
	}
	// Confirm the leading params are witnesses (the decl rewrite landed).
	first := sig.Params().At(0).Type()
	if !isWitnessType(first, fn.Dicts[0].Class) {
		return nil
	}
	return sig
}

// isWitnessType reports whether t is the witness struct of a class.
func isWitnessType(t types.Type, ref registry.ClassRef) bool {
	named, _ := types.Unalias(t).(*types.Named)
	if named == nil || named.Obj().Pkg() == nil {
		return false
	}
	return named.Obj().Pkg().Path() == ref.PkgPath && named.Obj().Name() == ref.Name
}

// dictAlreadyPassed reports whether the call's first arguments already
// carry the witnesses (explicit passing, or an earlier iteration's edit).
func dictAlreadyPassed(r *fileResolver, call *ast.CallExpr, fn *registry.ConstrainedFn, sig *types.Signature) bool {
	if len(call.Args) < len(fn.Dicts) {
		return false
	}
	info := r.pkg.TypesInfo
	for i, d := range fn.Dicts {
		tv, ok := info.Types[call.Args[i]]
		if !ok || tv.Type == nil {
			return false
		}
		if !isWitnessType(tv.Type, d.Class) {
			return false
		}
	}
	return true
}

// typeArgsFor determines the concrete (or type-param) type argument for
// each dictionary's tparam at one call site. nil result = wait.
func (r *fileResolver) typeArgsFor(call *ast.CallExpr, fnIdent *ast.Ident, sel *ast.SelectorExpr, fn *registry.ConstrainedFn, sig *types.Signature) ([]types.Type, error) {
	info := r.pkg.TypesInfo

	// Which signature tparam does each dict bind? Match by name.
	tparamIndex := map[string]int{}
	if tps := sig.TypeParams(); tps != nil {
		for i := 0; i < tps.Len(); i++ {
			tparamIndex[tps.At(i).Obj().Name()] = i
		}
	}

	resolveFromArgs := func() ([]types.Type, error) {
		// Structural unification of argument types against the original
		// parameters (the lowered signature minus the dictionaries).
		bound := make([]types.Type, len(fn.Dicts))
		params := sig.Params()
		for ai, arg := range call.Args {
			pi := ai + len(fn.Dicts)
			if pi >= params.Len() {
				break
			}
			tv, ok := info.Types[arg]
			if !ok || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
				continue
			}
			pt := params.At(pi).Type()
			if sig.Variadic() && pi == params.Len()-1 {
				if s, isSlice := pt.(*types.Slice); isSlice && !call.Ellipsis.IsValid() {
					pt = s.Elem()
				}
			}
			unifyInto(pt, types.Default(tv.Type), fn, bound)
		}
		for i := range bound {
			if bound[i] == nil {
				return nil, fmt.Errorf("cannot infer the type argument for %s in this call to %s; write %s[...](…)",
					fn.Dicts[i].TParam, fn.Name, fn.Name)
			}
		}
		return bound, nil
	}

	// (1) Explicit instantiation.
	var idxArgs []ast.Expr
	switch t := call.Fun.(type) {
	case *ast.IndexExpr:
		idxArgs = []ast.Expr{t.Index}
	case *ast.IndexListExpr:
		idxArgs = t.Indices
	}
	if idxArgs != nil {
		out := make([]types.Type, len(fn.Dicts))
		for i, d := range fn.Dicts {
			ti, ok := tparamIndex[d.TParam]
			if !ok || ti >= len(idxArgs) {
				return resolveFromArgs()
			}
			tv, tok := info.Types[idxArgs[ti]]
			if !tok || !tv.IsType() || tv.Type == types.Typ[types.Invalid] {
				return nil, nil // wait
			}
			out[i] = tv.Type
		}
		return out, nil
	}

	// (2) go/types instantiation fast path.
	if inst, ok := info.Instances[fnIdent]; ok && inst.TypeArgs != nil {
		out := make([]types.Type, len(fn.Dicts))
		good := true
		for i, d := range fn.Dicts {
			ti, found := tparamIndex[d.TParam]
			if !found || ti >= inst.TypeArgs.Len() {
				good = false
				break
			}
			at := inst.TypeArgs.At(ti)
			if at == nil || at == types.Typ[types.Invalid] {
				good = false
				break
			}
			out[i] = at
		}
		if good {
			return out, nil
		}
	}
	_ = sel

	// (3) Structural unification.
	return resolveFromArgs()
}

// unifyInto binds dict tparams occurring in param against the concrete
// arg type (structural, best-effort).
func unifyInto(param, arg types.Type, fn *registry.ConstrainedFn, bound []types.Type) {
	switch p := types.Unalias(param).(type) {
	case *types.TypeParam:
		name := p.Obj().Name()
		for i := range fn.Dicts {
			if fn.Dicts[i].TParam == name && bound[i] == nil {
				bound[i] = arg
			}
		}
	case *types.Slice:
		if a, ok := types.Unalias(arg).(*types.Slice); ok {
			unifyInto(p.Elem(), a.Elem(), fn, bound)
		}
	case *types.Array:
		if a, ok := types.Unalias(arg).(*types.Array); ok {
			unifyInto(p.Elem(), a.Elem(), fn, bound)
		}
	case *types.Pointer:
		if a, ok := types.Unalias(arg).(*types.Pointer); ok {
			unifyInto(p.Elem(), a.Elem(), fn, bound)
		}
	case *types.Map:
		if a, ok := types.Unalias(arg).(*types.Map); ok {
			unifyInto(p.Key(), a.Key(), fn, bound)
			unifyInto(p.Elem(), a.Elem(), fn, bound)
		}
	case *types.Chan:
		if a, ok := types.Unalias(arg).(*types.Chan); ok {
			unifyInto(p.Elem(), a.Elem(), fn, bound)
		}
	case *types.Signature:
		if a, ok := types.Unalias(arg).(*types.Signature); ok {
			for i := 0; i < p.Params().Len() && i < a.Params().Len(); i++ {
				unifyInto(p.Params().At(i).Type(), a.Params().At(i).Type(), fn, bound)
			}
			for i := 0; i < p.Results().Len() && i < a.Results().Len(); i++ {
				unifyInto(p.Results().At(i).Type(), a.Results().At(i).Type(), fn, bound)
			}
		}
	case *types.Named:
		if a, ok := types.Unalias(arg).(*types.Named); ok {
			pa, aa := p.TypeArgs(), a.TypeArgs()
			if pa != nil && aa != nil && pa.Len() == aa.Len() {
				for i := 0; i < pa.Len(); i++ {
					unifyInto(pa.At(i), aa.At(i), fn, bound)
				}
			}
		}
	}
}

// dictExprFor finds the witness expression for one dictionary at a call
// site: the enclosing function's own dictionary (upcast as needed) when
// the type argument is a type parameter, an instance search otherwise.
func (r *fileResolver) dictExprFor(call *ast.CallExpr, d registry.DictParam, targ types.Type) (string, bool) {
	if tp, isTP := types.Unalias(targ).(*types.TypeParam); isTP {
		return r.enclosingDictExpr(call, d, tp)
	}
	return r.searchInstance(call, d, targ)
}

// enclosingDictExpr threads the caller's own dictionary (locked: no
// search for type-param arguments; upcast when the callee's class is an
// ancestor).
func (r *fileResolver) enclosingDictExpr(call *ast.CallExpr, d registry.DictParam, tp *types.TypeParam) (string, bool) {
	encl := r.enclosingWitnessContext(call)
	if encl == nil {
		if r.report {
			r.errorf(call.Pos(), "cannot satisfy a %s constraint for a type parameter outside a constrained function", d.Class.Name)
		}
		return "", false
	}
	for _, have := range encl.dicts {
		if have.tparam != tp.Obj().Name() {
			continue
		}
		if have.class == d.Class {
			return have.expr, true
		}
		if r.reg.SubsumesRef(have.class, d.Class) {
			return have.expr + ".As" + d.Class.Name + "()", true
		}
	}
	if r.report {
		r.errorf(call.Pos(), "cannot satisfy the %s constraint here: add %s to this function's constraints or pass a witness explicitly",
			d.Class.Name, d.Class.Name)
	}
	return "", false
}

// searchInstance finds the unique in-scope instance for (class, concrete
// type): candidates are this package's instances plus exported instances
// of the file's direct imports; an instance of a stronger class satisfies
// a weaker constraint through its upcast.
func (r *fileResolver) searchInstance(call *ast.CallExpr, d registry.DictParam, targ types.Type) (string, bool) {
	type candidate struct {
		inst  *registry.Instance
		targs string // generic instantiation text; "" for ground
	}
	var cands []candidate
	consider := func(inst *registry.Instance) {
		if !r.reg.SubsumesRef(inst.Class, d.Class) {
			return
		}
		if !inst.Generic {
			it := r.instanceTypeArg(inst)
			if it != nil && types.Identical(it, targ) {
				cands = append(cands, candidate{inst: inst})
			}
			return
		}
		if text, ok := r.unifyGenericInstance(inst, targ); ok {
			cands = append(cands, candidate{inst: inst, targs: text})
		}
	}
	for _, inst := range r.reg.InstancesInPkg(r.pkg.PkgPath) {
		consider(inst)
	}
	for _, imp := range r.file.Imports {
		path, err := strconv.Unquote(imp.Path.Value)
		if err != nil || path == r.pkg.PkgPath {
			continue
		}
		for _, inst := range r.reg.InstancesInPkg(path) {
			if inst.Exported() {
				consider(inst)
			}
		}
	}

	switch len(cands) {
	case 0:
		if r.report {
			r.errorf(call.Pos(), "no instance of %s[%s] is in scope for this call; declare one, import a package that provides one, or pass a witness explicitly",
				d.Class.Name, r.localTypeString(targ))
		}
		return "", false
	case 1:
		c := cands[0]
		expr, ok := r.instanceExpr(c.inst, c.targs)
		if !ok {
			return "", false
		}
		if c.inst.Class != d.Class {
			expr += ".As" + d.Class.Name + "()"
		}
		return expr, true
	default:
		if r.report {
			var names []string
			for _, c := range cands {
				n := c.inst.Name
				if c.inst.PkgPath != r.pkg.PkgPath {
					n += " (" + c.inst.PkgPath + ")"
				}
				names = append(names, n)
			}
			r.errorf(call.Pos(), "ambiguous instance for %s[%s]: candidates %s; pass a witness explicitly",
				d.Class.Name, r.localTypeString(targ), strings.Join(names, ", "))
		}
		return "", false
	}
}

// instanceTypeArg evaluates a ground instance's type argument in its own
// package.
func (r *fileResolver) instanceTypeArg(inst *registry.Instance) types.Type {
	pkg := r.typesByPath[inst.PkgPath]
	if pkg == nil {
		return nil
	}
	obj := pkg.Scope().Lookup(inst.Name)
	if obj == nil {
		return nil
	}
	named, _ := types.Unalias(obj.Type()).(*types.Named)
	if named == nil || named.TypeArgs() == nil || named.TypeArgs().Len() != 1 {
		return nil
	}
	return named.TypeArgs().At(0)
}

// unifyGenericInstance unifies a generic instance's head type argument
// (e.g. []T) against the wanted concrete type, returning the rendered
// instantiation text ("int") on success.
func (r *fileResolver) unifyGenericInstance(inst *registry.Instance, targ types.Type) (string, bool) {
	pkg := r.typesByPath[inst.PkgPath]
	if pkg == nil {
		return "", false
	}
	obj := pkg.Scope().Lookup(inst.Name)
	if obj == nil {
		return "", false
	}
	sig, _ := obj.Type().(*types.Signature)
	if sig == nil || sig.Results().Len() != 1 || sig.TypeParams() == nil {
		return "", false
	}
	witness, _ := types.Unalias(sig.Results().At(0).Type()).(*types.Named)
	if witness == nil || witness.TypeArgs() == nil || witness.TypeArgs().Len() != 1 {
		return "", false
	}
	head := witness.TypeArgs().At(0)
	tps := sig.TypeParams()
	bound := make([]types.Type, tps.Len())
	if !unifyHead(head, targ, tps, bound) {
		return "", false
	}
	var texts []string
	for i := range bound {
		if bound[i] == nil {
			return "", false
		}
		text, err := r.typeText(bound[i])
		if err != nil {
			return "", false
		}
		texts = append(texts, text)
	}
	return strings.Join(texts, ", "), true
}

// unifyHead unifies an instance head type (containing the instance's own
// tparams) against a concrete type.
func unifyHead(head, targ types.Type, tps *types.TypeParamList, bound []types.Type) bool {
	switch h := types.Unalias(head).(type) {
	case *types.TypeParam:
		for i := 0; i < tps.Len(); i++ {
			if tps.At(i).Obj() == h.Obj() {
				if bound[i] == nil {
					bound[i] = targ
					return true
				}
				return types.Identical(bound[i], targ)
			}
		}
		return false
	case *types.Slice:
		a, ok := types.Unalias(targ).(*types.Slice)
		return ok && unifyHead(h.Elem(), a.Elem(), tps, bound)
	case *types.Array:
		a, ok := types.Unalias(targ).(*types.Array)
		return ok && h.Len() == a.Len() && unifyHead(h.Elem(), a.Elem(), tps, bound)
	case *types.Pointer:
		a, ok := types.Unalias(targ).(*types.Pointer)
		return ok && unifyHead(h.Elem(), a.Elem(), tps, bound)
	case *types.Map:
		a, ok := types.Unalias(targ).(*types.Map)
		return ok && unifyHead(h.Key(), a.Key(), tps, bound) && unifyHead(h.Elem(), a.Elem(), tps, bound)
	case *types.Chan:
		a, ok := types.Unalias(targ).(*types.Chan)
		return ok && unifyHead(h.Elem(), a.Elem(), tps, bound)
	case *types.Named:
		a, ok := types.Unalias(targ).(*types.Named)
		if !ok || h.Obj() != a.Obj() {
			return false
		}
		ha, aa := h.TypeArgs(), a.TypeArgs()
		if ha == nil || aa == nil || ha.Len() != aa.Len() {
			return ha == aa
		}
		for i := 0; i < ha.Len(); i++ {
			if !unifyHead(ha.At(i), aa.At(i), tps, bound) {
				return false
			}
		}
		return true
	default:
		return types.Identical(head, targ)
	}
}

// instanceExpr renders an instance reference in this file's namespace.
func (r *fileResolver) instanceExpr(inst *registry.Instance, targs string) (string, bool) {
	name := inst.Name
	if inst.PkgPath != r.pkg.PkgPath {
		alias, ok := r.importName(inst.PkgPath)
		if !ok {
			r.errorf(token.NoPos, "using instance %s requires importing %q", inst.Name, inst.PkgPath)
			return "", false
		}
		name = alias + "." + name
	}
	if inst.Generic {
		return name + "[" + targs + "]()", true
	}
	return name, true
}

// witnessDict is one in-scope dictionary: the expression that reaches it
// plus its class.
type witnessDict struct {
	tparam string
	class  registry.ClassRef
	expr   string
}

// witnessContext describes the witness scope of a generated declaration.
type witnessContext struct {
	dicts []witnessDict
}

// enclosingWitnessContext finds the dictionaries in scope at a node:
// a constrained function's dict params, a Law*/Default* method's
// receiver, or an instance constructor's witness temp.
func (r *fileResolver) enclosingWitnessContext(n ast.Node) *witnessContext {
	for node := n; node != nil; node = r.parents[node] {
		fd, ok := node.(*ast.FuncDecl)
		if !ok {
			continue
		}
		// Constrained function.
		if fn, found := r.reg.LookupConstrainedFn(r.pkg.PkgPath, fd.Name.Name); found && fd.Recv == nil && hasFnMarker(fd) {
			ctx := &witnessContext{}
			for _, d := range fn.Dicts {
				ctx.dicts = append(ctx.dicts, witnessDict{tparam: d.TParam, class: d.Class, expr: d.ParamName})
			}
			return ctx
		}
		// Law/Default witness method.
		if fd.Recv != nil && fd.Doc != nil {
			for _, c := range fd.Doc.List {
				m, isLaw := directive.ParseLawMarker(c.Text)
				if !isLaw {
					m, isLaw = directive.ParseDefaultMarker(c.Text)
				}
				if !isLaw {
					continue
				}
				recvName := ""
				if len(fd.Recv.List) > 0 && len(fd.Recv.List[0].Names) > 0 {
					recvName = fd.Recv.List[0].Names[0].Name
				}
				if recvName == "" {
					return nil
				}
				return &witnessContext{dicts: []witnessDict{{
					tparam: m.ClassTParam,
					class:  registry.ClassRef{PkgPath: r.pkg.PkgPath, Name: m.ClassName},
					expr:   recvName,
				}}}
			}
		}
		return nil
	}
	// Instance constructors are function literals inside marked decls;
	// walk again looking for the marker on the enclosing GenDecl/FuncDecl.
	return r.instanceWitnessContext(n)
}

// instanceWitnessContext finds the `w` scope inside an instance
// constructor.
func (r *fileResolver) instanceWitnessContext(n ast.Node) *witnessContext {
	for node := n; node != nil; node = r.parents[node] {
		var doc *ast.CommentGroup
		switch d := node.(type) {
		case *ast.GenDecl:
			doc = d.Doc
		case *ast.FuncDecl:
			doc = d.Doc
		default:
			continue
		}
		if doc == nil {
			return nil
		}
		for _, c := range doc.List {
			m, ok := directive.ParseInstanceMarker(c.Text)
			if !ok {
				continue
			}
			inst, found := r.reg.LookupInstance(r.pkg.PkgPath, m.Name)
			if !found {
				return nil
			}
			w := r.instanceTempName(node)
			if w == "" {
				return nil
			}
			return &witnessContext{dicts: []witnessDict{{
				tparam: "",
				class:  inst.Class,
				expr:   w,
			}}}
		}
		return nil
	}
	return nil
}

// instanceTempName finds the constructor's witness temp (`w := &C{…}`).
func (r *fileResolver) instanceTempName(decl ast.Node) string {
	name := ""
	ast.Inspect(decl, func(n ast.Node) bool {
		if name != "" {
			return false
		}
		as, ok := n.(*ast.AssignStmt)
		if !ok || as.Tok != token.DEFINE || len(as.Lhs) != 1 || len(as.Rhs) != 1 {
			return true
		}
		if _, isUnary := as.Rhs[0].(*ast.UnaryExpr); !isUnary {
			return true
		}
		if id, isID := as.Lhs[0].(*ast.Ident); isID {
			name = id.Name
		}
		return true
	})
	return name
}
