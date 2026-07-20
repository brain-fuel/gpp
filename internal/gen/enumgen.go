package gen

import (
	"fmt"
	"go/ast"
	"go/token"
	"strings"

	"goforge.dev/goplus/internal/core"
	"goforge.dev/goplus/internal/diag"
	"goforge.dev/goplus/internal/directive"
	"goforge.dev/goplus/internal/lower"
	"goforge.dev/goplus/internal/naming"
	"goforge.dev/goplus/internal/registry"
	"goforge.dev/goplus/internal/syntax"
)

// enumPlan is the package-wide enum analysis: render-ready specs plus the
// registry model used by resolution.
type enumPlan struct {
	specs     map[*syntax.EnumDecl]*lower.EnumSpec
	models    []*registry.Enum
	order     []*syntax.EnumDecl // declaration order
	model     map[*syntax.EnumDecl]*registry.Enum
	isIndexed registry.IndexArity
}

// planEnums assigns lowered names (detecting variant names shared across
// enums, which force enum-prefixed struct names), validates GADT result
// types, and builds render specs. Generated names are reserved in tbl.
func planEnums(idx *pkgIndex, pkgPath string, tbl *naming.Table, probe domainProbeFn) (*enumPlan, []diag.Diagnostic) {
	plan := &enumPlan{specs: map[*syntax.EnumDecl]*lower.EnumSpec{}, model: map[*syntax.EnumDecl]*registry.Enum{}}
	var diags []diag.Diagnostic

	type located struct {
		f *sourceFile
		e *syntax.EnumDecl
	}
	var all []located
	shared := map[string]int{} // goplus variant name -> #enums declaring it
	for _, f := range idx.files {
		if f.gp == nil {
			continue
		}
		for _, e := range f.gp.Enums {
			all = append(all, located{f, e})
			for _, v := range e.Variants {
				shared[v.Name.Name]++
			}
		}
	}

	// Indexed enums (v0.7.0): which package enums carry value indices,
	// and at which argument positions. Erasure and validation consult
	// this for every instantiation text (same-package references only;
	// cross-package indexed fields are a documented v1 restriction).
	type indexInfo struct {
		idx   map[int]bool
		arity int
	}
	indexedArity := map[string]indexInfo{}
	for _, le := range all {
		tp := le.e.Spec.TypeParams
		if tp == nil {
			continue
		}
		src := le.f.gp
		pos, idxSet := 0, map[int]bool{}
		for _, field := range tp.List {
			ctext := string(src.Src[src.Offset(field.Type.Pos()):src.Offset(field.Type.End())])
			for range field.Names {
				if ctext == "nat" {
					idxSet[pos] = true
				}
				pos++
			}
		}
		if len(idxSet) > 0 {
			indexedArity[le.e.Spec.Name.Name] = indexInfo{idx: idxSet, arity: pos}
		}
	}
	isIndexed := func(name string) (map[int]bool, int, bool) {
		info, ok := indexedArity[name]
		return info.idx, info.arity, ok
	}
	plan.isIndexed = isIndexed

	// probeDomain classifies a QUALIFIED constraint (states.State) as an
	// imported index domain via the dependency's markers.
	probeDomain := func(f *sourceFile, ctext string) (*registry.Enum, string, bool) {
		i := strings.LastIndex(ctext, ".")
		if i <= 0 || probe == nil {
			return nil, "", false
		}
		alias, base := ctext[:i], ctext[i+1:]
		path := ""
		for _, imp := range f.gp.AST.Imports {
			p := strings.Trim(imp.Path.Value, "\"")
			a := p[strings.LastIndex(p, "/")+1:]
			if imp.Name != nil && imp.Name.Name != "_" {
				a = imp.Name.Name
			}
			if a == alias {
				path = p
			}
		}
		if path == "" {
			return nil, "", false
		}
		es, ok := probe(path)
		if !ok {
			return nil, "", false
		}
		for _, de := range es {
			if de.Name == base && de.IsDomain {
				return de, path, true
			}
		}
		return nil, "", false
	}

	// Tag domains (v0.7.0 4b/4c): a type-parameter-less enum is a
	// first-order index domain when every variant's parameters are
	// themselves index-sorted (nat or another domain). Bare tags have
	// arity 0; structured tags (`Circle(r nat)`) carry their arity.
	tagDomains := map[string]map[string]int{}
	candidates := map[string]*located{}
	for i := range all {
		le := all[i]
		if le.e.Spec.TypeParams == nil {
			candidates[le.e.Spec.Name.Name] = &all[i]
		}
	}
	for changed := true; changed; {
		changed = false
		for name, le := range candidates {
			if tagDomains[name] != nil {
				continue
			}
			src := le.f.gp
			okDomain := true
			tags := map[string]int{}
			for _, v := range le.e.Variants {
				if v.TParams != nil || v.Result != nil {
					okDomain = false
					break
				}
				arity := 0
				if v.Params != nil {
					for _, fld := range v.Params.List {
						ptext := string(src.Src[src.Offset(fld.Type.Pos()):src.Offset(fld.Type.End())])
						if ptext != "nat" && tagDomains[ptext] == nil {
							okDomain = false
						}
						arity += len(fld.Names)
					}
				}
				if !okDomain {
					break
				}
				tags[v.Name.Name] = arity
			}
			if okDomain && len(tags) > 0 {
				tagDomains[name] = tags
				changed = true
			}
		}
	}

	for _, le := range all {
		f, e := le.f, le.e
		src := f.gp
		enumName := e.Spec.Name.Name
		errAt := func(pos token.Pos, format string, args ...any) {
			diags = append(diags, diag.At(idx.fset.Position(pos), format, args...))
		}

		if len(e.Gen.Specs) > 1 {
			errAt(e.Spec.Pos(), "declare each enum in its own type declaration (enum %s is inside a grouped type block)", enumName)
			continue
		}
		if len(e.Variants) == 0 {
			errAt(e.EnumPos, "enum %s must declare at least one variant", enumName)
			continue
		}

		// Partition binders: type parameters survive erasure; `n nat`
		// binders are value indices that exist only at check time.
		var tparamNames []string // ERASED type-parameter names
		var tparamConstraints []string
		var indices []registry.IndexBinder
		indexNames := map[string]bool{}
		binderSort := map[string]string{}
		kindIndex := []bool{}  // per ORIGINAL binder position
		kindSort := []string{} // sort at index positions ("" for type binders)
		origTParamsSrc := ""
		if tp := e.Spec.TypeParams; tp != nil {
			origTParamsSrc = string(src.Src[src.Offset(tp.Opening)+1 : src.Offset(tp.Closing)])
			pos := 0
			for _, field := range tp.List {
				ctext := string(src.Src[src.Offset(field.Type.Pos()):src.Offset(field.Type.End())])
				for _, n := range field.Names {
					if de, dpath, isImported := probeDomain(f, ctext); isImported {
						indices = append(indices, registry.IndexBinder{Name: n.Name, Sort: ctext, SortPkg: dpath, Pos: pos})
						indexNames[n.Name] = true
						binderSort[n.Name] = registry.SortBase(ctext)
						kindIndex = append(kindIndex, true)
						kindSort = append(kindSort, registry.SortBase(ctext))
						if tagDomains[registry.SortBase(ctext)] == nil {
							tagDomains[registry.SortBase(ctext)] = de.DomainTags()
						}
						pos++
						continue
					}
					if ctext == "nat" || tagDomains[ctext] != nil {
						indices = append(indices, registry.IndexBinder{Name: n.Name, Sort: ctext, Pos: pos})
						indexNames[n.Name] = true
						binderSort[n.Name] = ctext
						kindIndex = append(kindIndex, true)
						kindSort = append(kindSort, ctext)
					} else {
						tparamNames = append(tparamNames, n.Name)
						tparamConstraints = append(tparamConstraints, ctext)
						kindIndex = append(kindIndex, false)
						kindSort = append(kindSort, "")
					}
					pos++
				}
			}
		}
		tparamsSrc := origTParamsSrc
		if len(indices) > 0 {
			var kept []string
			for i, n := range tparamNames {
				kept = append(kept, n+" "+tparamConstraints[i])
			}
			tparamsSrc = strings.Join(kept, ", ")
		}
		indexResolver := goplusCallResolver(pkgPath, f.gp.AST)

		spec := &lower.EnumSpec{
			Name:        enumName,
			TParamsSrc:  tparamsSrc,
			TParamNames: tparamNames,
			MarkerName:  naming.MarkerMethodName(enumName),
			EnumMarker:  directive.EnumMarker{Name: enumName, TParams: origTParamsSrc}.String(),
		}
		model := &registry.Enum{PkgPath: pkgPath, Name: enumName, TParams: tparamNames, Indices: indices, IsDomain: tagDomains[enumName] != nil}
		ok := true

		for _, v := range e.Variants {
			vName := v.Name.Name
			typeName := naming.VariantTypeName(enumName, vName, shared[vName] > 1)
			origin := fmt.Sprintf("variant (%s) %s at %s", enumName, vName, idx.fset.Position(v.Name.Pos()))
			if err := tbl.AddGenerated(typeName, origin); err != nil {
				diags = append(diags, diag.Errorf("%s", err))
				ok = false
				continue
			}

			occurs, markerArgs, subst, resultArgs, indexArgs, rerr := analyzeResult(src, e, v, tparamNames, kindIndex, kindSort, indexNames, binderSort, tagDomains, isIndexed, indexResolver)
			if rerr != nil {
				errAt(v.Name.Pos(), "%v", rerr)
				ok = false
				continue
			}
			occursNames := map[string]bool{}
			for _, oi := range occurs {
				occursNames[tparamNames[oi]] = true
			}

			// Bounded existentials (v0.6.0): variant-level type parameters
			// erase to their interface bounds at every boundary.
			existSubst := map[string]string{}
			var existTPs []registry.ExistTP
			tparamsText := ""
			if v.TParams != nil {
				tparamsText = string(src.Src[src.Offset(v.TParams.Opening)+1 : src.Offset(v.TParams.Closing)])
				usedByField := map[string]bool{}
				if v.Params != nil {
					for _, field := range v.Params.List {
						for _, name := range tparamOccurrences(field.Type) {
							usedByField[name] = true
						}
					}
				}
				resultNames := map[string]bool{}
				if v.Result != nil {
					for _, name := range tparamOccurrences(v.Result) {
						resultNames[name] = true
					}
				}
				for _, field := range v.TParams.List {
					boundText := string(src.Src[src.Offset(field.Type.Pos()):src.Offset(field.Type.End())])
					for _, n := range field.Names {
						name := n.Name
						if boundText == "any" || strings.Contains(boundText, "|") || strings.Contains(boundText, "~") {
							errAt(n.Pos(), "existential type parameter %s of variant %s must have a plain interface bound: Go cannot express a match arm generic in a hidden type; give %s an interface bound or store the composition instead",
								name, vName, name)
							ok = false
							continue
						}
						for i, tn := range tparamNames {
							_ = i
							if tn == name {
								errAt(n.Pos(), "existential type parameter %s of variant %s shadows the enum's type parameter %s", name, vName, tn)
								ok = false
							}
						}
						if resultNames[name] {
							errAt(n.Pos(), "existential type parameter %s of variant %s must not appear in the result type; existentials are erased at the constructor boundary", name, vName)
							ok = false
						}
						if !usedByField[name] {
							errAt(n.Pos(), "existential type parameter %s of variant %s is not used by any field", name, vName)
							ok = false
						}
						for _, bn := range tparamOccurrences(field.Type) {
							isEnumTP := false
							for _, tn := range tparamNames {
								if tn == bn {
									isEnumTP = true
								}
							}
							if isEnumTP && !occursNames[bn] {
								if _, grounded := subst[bn]; !grounded {
									errAt(field.Type.Pos(), "variant %s: bound %s of %s references type parameter %s, which the variant does not carry",
										vName, boundText, name, bn)
									ok = false
								}
							}
						}
						existSubst[name] = boundText
						existTPs = append(existTPs, registry.ExistTP{Name: name, Bound: boundText})
					}
				}
			}

			vs := lower.EnumVariantSpec{GoplusName: vName, TypeName: typeName, MarkerArgs: markerArgs}
			if v.Doc != nil {
				var db strings.Builder
				for _, c := range v.Doc.List {
					db.WriteString(c.Text)
					db.WriteString("\n")
				}
				vs.Doc = db.String()
			}
			var keptSrcs []string
			for _, ki := range occurs {
				keptSrcs = append(keptSrcs, tparamNames[ki]+" "+tparamConstraints[ki])
				vs.TParamNames = append(vs.TParamNames, tparamNames[ki])
			}
			vs.TParamsSrc = strings.Join(keptSrcs, ", ")

			mv := &registry.EnumVariant{
				Name:       vName,
				TypeName:   typeName,
				HasParams:  v.Params != nil,
				ResultArgs: resultArgs,
				IndexArgs:  indexArgs,
				Occurs:     occurs,
				Exist:      existTPs,
			}
			exported := ast.IsExported(typeName)
			paramsSrc := ""
			if v.Params != nil {
				paramsSrc = string(src.Src[src.Offset(v.Params.Opening)+1 : src.Offset(v.Params.Closing)])
				for _, field := range v.Params.List {
					declType := string(src.Src[src.Offset(field.Type.Pos()):src.Offset(field.Type.End())])
					// A field referencing an enum tparam the variant neither
					// carries nor grounds is an implicit unbounded
					// existential — impossible under Go's erasure.
					for _, name := range tparamOccurrences(field.Type) {
						_, isTP := func() (int, bool) {
							for i, n := range tparamNames {
								if n == name {
									return i, true
								}
							}
							return 0, false
						}()
						if isTP && !occursNames[name] {
							if _, grounded := subst[name]; !grounded {
								errAt(field.Type.Pos(),
									"variant %s: type parameter %s does not appear in the result type %s and is unconstrained; pin it in the result type or declare a bounded variant-level type parameter",
									vName, name, string(src.Src[src.Offset(v.Result.Pos()):src.Offset(v.Result.End())]))
								ok = false
							}
						}
					}
					erased, droppedTerms, ierr := registry.EraseCollectIndexArgs(declType, isIndexed)
					if ierr != nil {
						errAt(field.Type.Pos(), "%v", ierr)
						ok = false
						continue
					}
					if strings.Contains(erased, "nat") {
						// nat-typed fields (index-domain enums) erase to int.
						if ne, nerr := substituteTypeText(erased, map[string]string{"nat": "int"}); nerr == nil {
							erased = ne
						}
					}
					for _, dt := range droppedTerms {
						if verr := validIndexTerm(dt, "", indexNames, binderSort, tagDomains, indexResolver); verr != nil {
							errAt(field.Type.Pos(), "variant %s: %v", vName, verr)
							ok = false
						}
					}
					if len(existSubst) > 0 {
						var eerr error
						erased, eerr = substituteTypeText(erased, existSubst)
						if eerr != nil {
							errAt(field.Type.Pos(), "%v", eerr)
							ok = false
							continue
						}
					}
					fieldType, serr := substituteTypeText(erased, subst)
					if serr != nil {
						errAt(field.Type.Pos(), "%v", serr)
						ok = false
						continue
					}
					for _, n := range field.Names {
						if n.Name == "_" {
							errAt(n.Pos(), "enum variant fields must not be blank")
							ok = false
							continue
						}
						mv.Params = append(mv.Params, registry.EnumParam{
							Name:      n.Name,
							FieldName: naming.FieldName(n.Name, exported),
							Type:      erased,
							RawType:   declType,
						})
						vs.Fields = append(vs.Fields, lower.FieldSpec{
							Name: naming.FieldName(n.Name, exported),
							Type: fieldType,
						})
						vs.ParamNames = append(vs.ParamNames, n.Name)
					}
				}
			}
			resultText := ""
			if v.Result != nil {
				resultText = string(src.Src[src.Offset(v.Result.Pos()):src.Offset(v.Result.End())])
			}
			vs.Marker = directive.VariantMarker{
				EnumName:    enumName,
				EnumTParams: strings.Join(tparamNames, ", "),
				Name:        vName,
				TParams:     tparamsText,
				Params:      paramsSrc,
				HasParams:   v.Params != nil,
				Result:      resultText,
			}.String()

			spec.Variants = append(spec.Variants, vs)
			model.Variants = append(model.Variants, mv)
		}
		if !ok {
			continue
		}
		plan.specs[e] = spec
		plan.models = append(plan.models, model)
		plan.order = append(plan.order, e)
		plan.model[e] = model
	}
	return plan, diags
}

// analyzeResult analyzes a variant's (explicit or defaulted) result type
// under the v0.6.0 structural model: each result position may be an
// arbitrary type expression. It reports the OCCURRING enum type
// parameters (those appearing anywhere in the result arguments — the
// variant struct's type parameters, in enum order), the sealed-method
// argument texts (verbatim), the ground substitution for eliminated
// parameters (a fully ground position whose own parameter occurs
// nowhere), and the raw result argument texts (nil if defaulted).
func analyzeResult(src *syntax.File, e *syntax.EnumDecl, v *syntax.Variant, tparamNames []string,
	kindIndex []bool, kindSort []string, indexNames map[string]bool, binderSort map[string]string,
	tagDomains map[string]map[string]int, isIndexed registry.IndexArity, indexResolver core.CallResolver) (
	occurs []int, markerArgs []string, subst map[string]string, resultArgs []string, indexArgs []string, err error) {

	enumName := e.Spec.Name.Name
	if v.Result == nil {
		for i, n := range tparamNames {
			occurs = append(occurs, i)
			markerArgs = append(markerArgs, n)
		}
		// A defaulted result leaves every index unconstrained: the index
		// argument is the binder itself.
		pos := 0
		for _, isIdx := range kindIndex {
			if isIdx {
				indexArgs = append(indexArgs, indexBinderNameAt(kindIndex, indexNames, e, src, pos))
			}
			pos++
		}
		return occurs, markerArgs, nil, nil, indexArgs, nil
	}

	base, args := decomposeResult(v.Result)
	if base == nil || base.Name != enumName {
		return nil, nil, nil, nil, nil, fmt.Errorf("variant %s: result type must be %s applied to type arguments", v.Name.Name, enumName)
	}
	if len(args) != len(kindIndex) {
		return nil, nil, nil, nil, nil, fmt.Errorf("variant %s: result type has %d arguments but %s declares %d parameters",
			v.Name.Name, len(args), enumName, len(kindIndex))
	}

	// Partition the result arguments by binder kind.
	var typeArgs []ast.Expr
	for i, arg := range args {
		text := string(src.Src[src.Offset(arg.Pos()):src.Offset(arg.End())])
		if kindIndex[i] {
			if verr := validIndexTerm(text, kindSort[i], indexNames, binderSort, tagDomains, indexResolver); verr != nil {
				return nil, nil, nil, nil, nil, fmt.Errorf("variant %s: %v", v.Name.Name, verr)
			}
			indexArgs = append(indexArgs, text)
			continue
		}
		for _, name := range tparamOccurrences(arg) {
			if indexNames[name] {
				return nil, nil, nil, nil, nil, fmt.Errorf("variant %s: index parameter %s cannot be used as a type", v.Name.Name, name)
			}
		}
		typeArgs = append(typeArgs, arg)
	}

	tparamSet := map[string]int{}
	for i, n := range tparamNames {
		tparamSet[n] = i
	}
	occursSet := map[int]bool{}
	ground := make([]bool, len(typeArgs))
	for i, arg := range typeArgs {
		text := string(src.Src[src.Offset(arg.Pos()):src.Offset(arg.End())])
		erased, dropped, eerr := registry.EraseCollectIndexArgs(text, isIndexed)
		if eerr != nil {
			return nil, nil, nil, nil, nil, fmt.Errorf("variant %s: %v", v.Name.Name, eerr)
		}
		for _, dt := range dropped {
			if verr := validIndexTerm(dt, "", indexNames, binderSort, tagDomains, indexResolver); verr != nil {
				return nil, nil, nil, nil, nil, fmt.Errorf("variant %s: %v", v.Name.Name, verr)
			}
		}
		markerArgs = append(markerArgs, erased)
		resultArgs = append(resultArgs, erased)
		ground[i] = true
		for _, name := range tparamOccurrences(arg) {
			if _, isTP := tparamSet[name]; isTP {
				occursSet[tparamSet[name]] = true
				ground[i] = false
			}
		}
	}
	for i := range tparamNames {
		if occursSet[i] {
			occurs = append(occurs, i)
		}
	}
	subst = map[string]string{}
	for i := range typeArgs {
		if ground[i] && !occursSet[i] {
			subst[tparamNames[i]] = resultArgs[i]
		}
	}
	return occurs, markerArgs, subst, resultArgs, indexArgs, nil
}

// indexBinderNameAt recovers the binder name at an original tparam
// position (defaulted-result variants of indexed enums).
func indexBinderNameAt(kindIndex []bool, indexNames map[string]bool, e *syntax.EnumDecl, src *syntax.File, pos int) string {
	i := 0
	for _, field := range e.Spec.TypeParams.List {
		for _, n := range field.Names {
			if i == pos {
				return n.Name
			}
			i++
		}
	}
	return "_"
}

// validIndexTerm checks an index argument elaborates over the enum's
// index binders. sort "" accepts any well-formed index term (nested
// field positions); "nat" demands nat vocabulary; an enum sort demands
// one of its tags or a binder of that sort.
func validIndexTerm(text, sort string, indexNames map[string]bool, binderSort map[string]string,
	tagDomains map[string]map[string]int, resolve core.CallResolver) error {
	term, err := core.ParseIndexTerm(text, resolve)
	if err != nil {
		return fmt.Errorf("index argument %s must be an index expression: %v", text, err)
	}
	term = core.ResolveTags(term, func(name string) (string, bool) {
		for enum, tags := range tagDomains {
			if _, isTag := tags[name]; isTag {
				return enum, true
			}
		}
		return "", false
	})
	if sort != "" && sort != "nat" {
		switch x := term.(type) {
		case core.Ctor:
			if x.Type != sort {
				return fmt.Errorf("index argument %s is a %s tag, but this position is indexed by %s", text, x.Type, sort)
			}
			if want := tagDomains[sort][x.Name]; len(x.Args) != want {
				return fmt.Errorf("index argument %s: tag %s of %s takes %d arguments, got %d", text, x.Name, sort, want, len(x.Args))
			}
			for _, fv := range core.FreeVars(term) {
				if !indexNames[fv] {
					return fmt.Errorf("index argument %s uses %s, which is not an index parameter of the enum", text, fv)
				}
			}
			return nil
		case core.Var:
			if binderSort[x.Name] != sort {
				return fmt.Errorf("index argument %s is not a %s tag or a %s-sorted index parameter", text, sort, sort)
			}
			return nil
		default:
			return fmt.Errorf("index argument %s is not a %s tag or a %s-sorted index parameter", text, sort, sort)
		}
	}
	for _, fv := range core.FreeVars(term) {
		if !indexNames[fv] {
			return fmt.Errorf("index argument %s uses %s, which is not an index parameter of the enum", text, fv)
		}
	}
	if sort == "nat" {
		if bad := firstTagIn(term); bad != "" {
			return fmt.Errorf("index argument %s uses tag %s in a nat-indexed position", text, bad)
		}
	}
	return nil
}

// firstTagIn finds a constructor tag inside a term, if any.
func firstTagIn(t core.Term) string {
	switch x := t.(type) {
	case core.Ctor:
		return x.Name
	case core.Prim:
		for _, a := range x.Args {
			if b := firstTagIn(a); b != "" {
				return b
			}
		}
	case core.Call:
		for _, a := range x.Args {
			if b := firstTagIn(a); b != "" {
				return b
			}
		}
	}
	return ""
}

// tparamOccurrences lists identifier names occurring free in a type
// expression (selector .Sel names skipped — qualified types never name a
// type parameter).
func tparamOccurrences(e ast.Expr) []string {
	var out []string
	ast.Inspect(e, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.SelectorExpr:
			ast.Inspect(x.X, func(m ast.Node) bool {
				if id, ok := m.(*ast.Ident); ok {
					out = append(out, id.Name)
				}
				return true
			})
			return false
		case *ast.Ident:
			out = append(out, x.Name)
		}
		return true
	})
	return out
}

// decomposeResult splits `Expr[int, T]` (or bare `Shape`) into base ident
// and argument exprs.
func decomposeResult(result ast.Expr) (*ast.Ident, []ast.Expr) {
	switch r := result.(type) {
	case *ast.Ident:
		return r, nil
	case *ast.IndexExpr:
		if id, ok := r.X.(*ast.Ident); ok {
			return id, []ast.Expr{r.Index}
		}
	case *ast.IndexListExpr:
		if id, ok := r.X.(*ast.Ident); ok {
			return id, r.Indices
		}
	}
	return nil, nil
}

// rootDomainEnums scans a loaded package for index-domain enums
// (zero-binder, all variant parameters index-sorted) as minimal
// registry models — probeable by sibling roots during pass 1, before
// any generated file exists.
func rootDomainEnums(idx *pkgIndex, pkgPath string) []*registry.Enum {
	type cand struct {
		e *syntax.EnumDecl
		f *sourceFile
	}
	var cands []cand
	for _, f := range idx.files {
		if f.gp == nil {
			continue
		}
		for _, e := range f.gp.Enums {
			if e.Spec.TypeParams == nil {
				cands = append(cands, cand{e: e, f: f})
			}
		}
	}
	names := map[string]bool{}
	tags := map[string]map[string]int{}
	for changed := true; changed; {
		changed = false
		for _, c := range cands {
			name := c.e.Spec.Name.Name
			if names[name] {
				continue
			}
			src := c.f.gp
			okDomain := true
			t := map[string]int{}
			for _, v := range c.e.Variants {
				if v.TParams != nil || v.Result != nil {
					okDomain = false
					break
				}
				arity := 0
				if v.Params != nil {
					for _, fld := range v.Params.List {
						ptext := string(src.Src[src.Offset(fld.Type.Pos()):src.Offset(fld.Type.End())])
						if ptext != "nat" && !names[ptext] {
							okDomain = false
						}
						arity += len(fld.Names)
					}
				}
				if !okDomain {
					break
				}
				t[v.Name.Name] = arity
			}
			if okDomain && len(t) > 0 {
				names[name] = true
				tags[name] = t
				changed = true
			}
		}
	}
	var out []*registry.Enum
	for name, t := range tags {
		e := &registry.Enum{PkgPath: pkgPath, Name: name, IsDomain: true}
		for tag, arity := range t {
			v := &registry.EnumVariant{Name: tag, HasParams: arity > 0}
			for i := 0; i < arity; i++ {
				v.Params = append(v.Params, registry.EnumParam{Name: fmt.Sprintf("p%d", i), Type: "int"})
			}
			e.Variants = append(e.Variants, v)
		}
		out = append(out, e)
	}
	return out
}
