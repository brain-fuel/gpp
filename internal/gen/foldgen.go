package gen

import (
	"fmt"
	"strings"
	"unicode"
	"unicode/utf8"

	"goforge.dev/goplus/internal/directive"
	"goforge.dev/goplus/internal/lower"
	"goforge.dev/goplus/internal/naming"
	"goforge.dev/goplus/internal/syntax"
)

// Fold derivation (v0.6.0). Every enum derives, BY DEFAULT, a one-level
// fold in its own package:
//
//	type ExprCases[T any, R any] struct {
//		Lit func(v int) R
//		If  func(c Expr[bool], then Expr[T], els Expr[T]) R
//	}
//	func Fold[T any, R any](e Expr[T], cs ExprCases[T, R]) R { … }
//
// The fold function follows the v0.5.1 naming rule (bare Fold when
// unique — two deriving enums both prefix); the Cases struct is always
// enum-prefixed. `//goplus:derive off` on the enum suppresses derivation;
// an enum whose result arguments leave a variant's type parameters
// undetermined under the identity instantiation silently derives
// nothing (the same erasure wall as unmatchable arms).

// deriveMode reads the enum's //goplus:derive directive. "off" suppresses
// all derivation; "gen" (v0.10.0) additionally opts the enum into a
// standalone generator test file.
func deriveMode(e *syntax.EnumDecl) (off bool, genOptIn bool, unknown string) {
	if e.Gen == nil || e.Gen.Doc == nil {
		return false, false, ""
	}
	for _, c := range e.Gen.Doc.List {
		arg, ok := directive.ParseDeriveMarker(c.Text)
		if !ok {
			continue
		}
		switch arg {
		case "off":
			return true, false, ""
		case "gen":
			return false, true, ""
		}
		return false, false, arg
	}
	return false, false, ""
}

// foldHeadArgs computes the identity-instantiation head arguments for a
// variant: for each occurring tparam, the enum tparam name at the bare
// position that binds it. ok=false when some occurring tparam has no bare
// position (composite-only — underivable).
func foldHeadArgs(spec *lower.EnumSpec, vs *lower.EnumVariantSpec, resultArgs []string) ([]string, bool) {
	if len(vs.TParamNames) == 0 {
		return nil, true
	}
	if resultArgs == nil {
		return append([]string{}, vs.TParamNames...), true
	}
	out := make([]string, len(vs.TParamNames))
	for i, occName := range vs.TParamNames {
		found := ""
		for pi, pat := range resultArgs {
			if pat == occName && pi < len(spec.TParamNames) {
				found = spec.TParamNames[pi]
				break
			}
		}
		if found == "" {
			return nil, false
		}
		out[i] = found
	}
	return out, true
}

// planFolds names and renders each derivable enum's fold, reserving the
// generated names. It seeds the package's shared bare-name counts with
// exactly the DERIVING enums, so a lone derivable enum keeps the bare
// name even beside underivable or opted-out siblings.
func planFolds(idx *pkgIndex, plan *enumPlan, tbl *naming.Table, shared map[string]int) []error {
	var errs []error
	type job struct {
		e     *syntax.EnumDecl
		spec  *lower.EnumSpec
		cases []foldCase
	}
	var jobs []job
	for _, e := range plan.order {
		spec := plan.specs[e]
		model := plan.model[e]
		off, _, unknown := deriveMode(e)
		if unknown != "" {
			errs = append(errs, fmt.Errorf("%s: unknown //goplus:derive argument %q; supported arguments: 'off', 'gen'",
				idx.fset.Position(e.Spec.Pos()), unknown))
			continue
		}
		if off {
			continue
		}
		derivable := true
		var cases []foldCase
		for i := range spec.Variants {
			vs := &spec.Variants[i]
			var resultArgs []string
			if mv, mok := model.Variant(vs.GoplusName); mok {
				resultArgs = mv.ResultArgs
			}
			headArgs, ok := foldHeadArgs(spec, vs, resultArgs)
			if !ok {
				derivable = false
				break
			}
			head := vs.TypeName
			bind := map[string]string{}
			for hi, occName := range vs.TParamNames {
				bind[occName] = headArgs[hi]
			}
			if len(headArgs) > 0 {
				head += "[" + strings.Join(headArgs, ", ") + "]"
			}
			cases = append(cases, foldCase{vs: vs, head: head, bind: bind})
		}
		if !derivable {
			continue
		}
		shared[naming.BareName(spec.Name, "Fold")]++
		jobs = append(jobs, job{e: e, spec: spec, cases: cases})
	}

	for _, j := range jobs {
		e, spec, cases := j.e, j.spec, j.cases
		foldName := naming.FuncName(spec.Name, "Fold", shared)
		if bare := naming.BareName(spec.Name, "Fold"); foldName == bare && tbl.Has(bare) {
			foldName = naming.PrefixedName(spec.Name, "Fold")
		}
		casesName := naming.PrefixedName(spec.Name, "Cases")
		origin := fmt.Sprintf("derived Fold for enum %s at %s", spec.Name, idx.fset.Position(e.Spec.Pos()))
		if err := tbl.AddGenerated(foldName, origin); err != nil {
			errs = append(errs, err)
			continue
		}
		if err := tbl.AddGenerated(casesName, fmt.Sprintf("derived %s for enum %s at %s", casesName, spec.Name, idx.fset.Position(e.Spec.Pos()))); err != nil {
			errs = append(errs, err)
			continue
		}

		spec.FoldText = renderFold(spec, foldName, casesName, cases)
	}
	return errs
}

// foldCase pairs a variant spec with its identity-instantiation head and
// the simultaneous renaming its handler's parameter types need (struct
// tparam name -> identity head argument; cross-position variants swap).
type foldCase struct {
	vs   *lower.EnumVariantSpec
	head string
	bind map[string]string
}

func renderFold(spec *lower.EnumSpec, foldName, casesName string, cases []foldCase) string {
	tparams := "R any"
	tnames := "R"
	if spec.TParamsSrc != "" {
		tparams = spec.TParamsSrc + ", R any"
		tnames = strings.Join(spec.TParamNames, ", ") + ", R"
	}
	enumType := spec.Name
	if len(spec.TParamNames) > 0 {
		enumType += "[" + strings.Join(spec.TParamNames, ", ") + "]"
	}
	val := valueParamName(spec)

	var b strings.Builder
	fmt.Fprintf(&b, "// %s selects one handler per %s variant for %s.\n", casesName, spec.Name, foldName)
	fmt.Fprintf(&b, "type %s[%s] struct {\n", casesName, tparams)
	for _, c := range cases {
		var params []string
		for i, f := range c.vs.Fields {
			name := f.Name
			if i < len(c.vs.ParamNames) {
				name = c.vs.ParamNames[i]
			}
			ftype := f.Type
			if len(c.bind) > 0 {
				if sub, err := substituteTypeText(ftype, c.bind); err == nil {
					ftype = sub
				}
			}
			params = append(params, name+" "+ftype)
		}
		fmt.Fprintf(&b, "\t%s func(%s) R\n", c.vs.GoplusName, strings.Join(params, ", "))
	}
	b.WriteString("}\n\n")

	anyFields := false
	for _, c := range cases {
		if len(c.vs.Fields) > 0 {
			anyFields = true
		}
	}
	guard := "any(" + val + ").(type)"
	if anyFields {
		guard = "m := " + guard
	}
	fmt.Fprintf(&b, "// %s reduces %s by one-level case analysis.\n", foldName, enumType)
	fmt.Fprintf(&b, "func %s[%s](%s %s, cs %s[%s]) R {\n\tswitch %s {\n",
		foldName, tparams, val, enumType, casesName, tnames, guard)
	for _, c := range cases {
		fmt.Fprintf(&b, "\tcase %s:\n", c.head)
		var args []string
		for _, f := range c.vs.Fields {
			args = append(args, "m."+f.Name)
		}
		fmt.Fprintf(&b, "\t\treturn cs.%s(%s)\n", c.vs.GoplusName, strings.Join(args, ", "))
	}
	fmt.Fprintf(&b, "\tdefault:\n\t\tpanic(\"goplus: impossible enum value in %s\")\n\t}\n}\n", foldName)
	return b.String()
}

// valueParamName picks the fold's value parameter: the enum's first rune
// lowercased, avoiding collisions with tparams and "cs".
func valueParamName(spec *lower.EnumSpec) string {
	r, _ := utf8.DecodeRuneInString(spec.Name)
	cand := string(unicode.ToLower(r))
	if cand == "r" || cand == "c" {
		return "v"
	}
	for _, n := range spec.TParamNames {
		if strings.EqualFold(n, cand) {
			return "v"
		}
	}
	return cand
}
