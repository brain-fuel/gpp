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
}

// planEnums assigns lowered names (detecting variant names shared across
// enums, which force enum-prefixed struct names), validates GADT result
// types, and builds render specs. Generated names are reserved in tbl.
func planEnums(idx *pkgIndex, pkgPath string, tbl *naming.Table) (*enumPlan, []diag.Diagnostic) {
	plan := &enumPlan{specs: map[*syntax.EnumDecl]*lower.EnumSpec{}}
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
			if v.NameOverride != "" && !token.IsIdentifier(v.NameOverride) {
				errAt(v.Name.Pos(), "//gpp:name %q is not a valid Go identifier", v.NameOverride)
				ok = false
				continue
			}
			typeName := naming.VariantTypeName(enumName, vName, v.NameOverride, shared[vName] > 1)
			origin := fmt.Sprintf("variant (%s) %s at %s", enumName, vName, idx.fset.Position(v.Name.Pos()))
			if err := tbl.AddGenerated(typeName, origin); err != nil {
				diags = append(diags, diag.Errorf("%s", err))
				ok = false
				continue
			}

			kept, markerArgs, subst, resultArgs, rerr := analyzeResult(src, e, v, tparamNames)
			if rerr != nil {
				errAt(v.Name.Pos(), "%v", rerr)
				ok = false
				continue
			}

			vs := lower.EnumVariantSpec{TypeName: typeName, MarkerArgs: markerArgs}
			var keptSrcs []string
			for _, ki := range kept {
				keptSrcs = append(keptSrcs, tparamNames[ki]+" "+tparamConstraints[ki])
				vs.TParamNames = append(vs.TParamNames, tparamNames[ki])
			}
			vs.TParamsSrc = strings.Join(keptSrcs, ", ")

			mv := &registry.EnumVariant{
				Name:       vName,
				TypeName:   typeName,
				HasParams:  v.Params != nil,
				ResultArgs: resultArgs,
			}
			exported := ast.IsExported(typeName)
			paramsSrc := ""
			if v.Params != nil {
				paramsSrc = string(src.Src[src.Offset(v.Params.Opening)+1 : src.Offset(v.Params.Closing)])
				for _, field := range v.Params.List {
					declType := string(src.Src[src.Offset(field.Type.Pos()):src.Offset(field.Type.End())])
					fieldType, serr := substituteTypeText(declType, subst)
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
							Type:      declType,
						})
						vs.Fields = append(vs.Fields, lower.FieldSpec{
							Name: naming.FieldName(n.Name, exported),
							Type: fieldType,
						})
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
	}
	return plan, diags
}

// analyzeResult validates a variant's (explicit or defaulted) result type
// under the v0.2.0 restriction and reports which enum type parameters the
// variant keeps, the sealed-method argument texts, the substitution for
// fixed parameters, and the raw result argument texts (nil if defaulted).
func analyzeResult(src *syntax.File, e *syntax.EnumDecl, v *syntax.Variant, tparamNames []string) (
	kept []int, markerArgs []string, subst map[string]string, resultArgs []string, err error) {

	enumName := e.Spec.Name.Name
	if v.Result == nil {
		for i, n := range tparamNames {
			kept = append(kept, i)
			markerArgs = append(markerArgs, n)
		}
		return kept, markerArgs, nil, nil, nil
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
	subst = map[string]string{}
	for i, arg := range args {
		text := string(src.Src[src.Offset(arg.Pos()):src.Offset(arg.End())])
		switch a := arg.(type) {
		case *ast.Ident:
			if a.Name == tparamNames[i] {
				kept = append(kept, i)
				markerArgs = append(markerArgs, a.Name)
				resultArgs = append(resultArgs, text)
				continue
			}
			if _, isTParam := tparamSet[a.Name]; isTParam {
				return nil, nil, nil, nil, fmt.Errorf(
					"variant %s: unsupported result type %s: v0.2.0 supports the enum's own type parameter (in its own position) or a named type in each position",
					v.Name.Name, text)
			}
			markerArgs = append(markerArgs, text)
			subst[tparamNames[i]] = text
			resultArgs = append(resultArgs, text)
		case *ast.SelectorExpr:
			markerArgs = append(markerArgs, text)
			subst[tparamNames[i]] = text
			resultArgs = append(resultArgs, text)
		default:
			return nil, nil, nil, nil, fmt.Errorf(
				"variant %s: unsupported result type argument %s: v0.2.0 supports the enum's own type parameter or a named type in each position",
				v.Name.Name, text)
		}
	}
	return kept, markerArgs, subst, resultArgs, nil
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
