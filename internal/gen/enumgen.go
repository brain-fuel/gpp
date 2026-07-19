package gen

import (
	"fmt"
	"go/ast"
	"go/token"
	"strings"

	"goforge.dev/gpp/internal/diag"
	"goforge.dev/gpp/internal/directive"
	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/naming"
	"goforge.dev/gpp/internal/registry"
	"goforge.dev/gpp/internal/syntax"
)

// enumPlan is the package-wide enum analysis: render-ready specs plus the
// registry model used by resolution.
type enumPlan struct {
	specs  map[*syntax.EnumDecl]*lower.EnumSpec
	models []*registry.Enum
	order  []*syntax.EnumDecl              // declaration order
	model  map[*syntax.EnumDecl]*registry.Enum
}

// planEnums assigns lowered names (detecting variant names shared across
// enums, which force enum-prefixed struct names), validates GADT result
// types, and builds render specs. Generated names are reserved in tbl.
func planEnums(idx *pkgIndex, pkgPath string, tbl *naming.Table) (*enumPlan, []diag.Diagnostic) {
	plan := &enumPlan{specs: map[*syntax.EnumDecl]*lower.EnumSpec{}, model: map[*syntax.EnumDecl]*registry.Enum{}}
	var diags []diag.Diagnostic

	type located struct {
		f *sourceFile
		e *syntax.EnumDecl
	}
	var all []located
	shared := map[string]int{} // gpp variant name -> #enums declaring it
	for _, f := range idx.files {
		if f.gpp == nil {
			continue
		}
		for _, e := range f.gpp.Enums {
			all = append(all, located{f, e})
			for _, v := range e.Variants {
				shared[v.Name.Name]++
			}
		}
	}

	for _, le := range all {
		f, e := le.f, le.e
		src := f.gpp
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

		var tparamNames []string
		var tparamConstraints []string
		tparamsSrc := ""
		if tp := e.Spec.TypeParams; tp != nil {
			tparamsSrc = string(src.Src[src.Offset(tp.Opening)+1 : src.Offset(tp.Closing)])
			for _, field := range tp.List {
				ctext := string(src.Src[src.Offset(field.Type.Pos()):src.Offset(field.Type.End())])
				for _, n := range field.Names {
					tparamNames = append(tparamNames, n.Name)
					tparamConstraints = append(tparamConstraints, ctext)
				}
			}
		}

		spec := &lower.EnumSpec{
			Name:        enumName,
			TParamsSrc:  tparamsSrc,
			TParamNames: tparamNames,
			MarkerName:  naming.MarkerMethodName(enumName),
			EnumMarker:  directive.EnumMarker{Name: enumName, TParams: tparamsSrc}.String(),
		}
		model := &registry.Enum{PkgPath: pkgPath, Name: enumName, TParams: tparamNames}
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

			occurs, markerArgs, subst, resultArgs, rerr := analyzeResult(src, e, v, tparamNames)
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

			vs := lower.EnumVariantSpec{GppName: vName, TypeName: typeName, MarkerArgs: markerArgs}
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
					erased := declType
					if len(existSubst) > 0 {
						var eerr error
						erased, eerr = substituteTypeText(declType, existSubst)
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
func analyzeResult(src *syntax.File, e *syntax.EnumDecl, v *syntax.Variant, tparamNames []string) (
	occurs []int, markerArgs []string, subst map[string]string, resultArgs []string, err error) {

	enumName := e.Spec.Name.Name
	if v.Result == nil {
		for i, n := range tparamNames {
			occurs = append(occurs, i)
			markerArgs = append(markerArgs, n)
		}
		return occurs, markerArgs, nil, nil, nil
	}

	base, args := decomposeResult(v.Result)
	if base == nil || base.Name != enumName {
		return nil, nil, nil, nil, fmt.Errorf("variant %s: result type must be %s applied to type arguments", v.Name.Name, enumName)
	}
	if len(args) != len(tparamNames) {
		return nil, nil, nil, nil, fmt.Errorf("variant %s: result type has %d type arguments but %s declares %d type parameters",
			v.Name.Name, len(args), enumName, len(tparamNames))
	}
	tparamSet := map[string]int{}
	for i, n := range tparamNames {
		tparamSet[n] = i
	}

	occursSet := map[int]bool{}
	ground := make([]bool, len(args))
	for i, arg := range args {
		text := string(src.Src[src.Offset(arg.Pos()):src.Offset(arg.End())])
		markerArgs = append(markerArgs, text)
		resultArgs = append(resultArgs, text)
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
	for i := range args {
		if ground[i] && !occursSet[i] {
			subst[tparamNames[i]] = resultArgs[i]
		}
	}
	return occurs, markerArgs, subst, resultArgs, nil
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
