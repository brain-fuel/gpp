package gen

import (
	"fmt"
	"go/format"
	"path/filepath"
	"regexp"
	"strings"

	"goforge.dev/goplus/internal/diag"
	"goforge.dev/goplus/internal/emit"
	"goforge.dev/goplus/internal/registry"
)

// Derived rapid generators (v0.10.0). Every MONOMORPHIC enum (no type
// parameters, no indices) can derive
//
//	func Gen<Enum>(t *rapid.T) <Enum>
//
// choosing a variant uniformly and generating fields recursively:
// rapid built-ins for base types, sibling generators for enum-typed
// fields (depth-bounded — at depth 0 only LEAF variants, those with no
// enum-typed fields, remain). Derivation is default-on; EMISSION is
// demand-driven (law tests that need one, or //goplus:derive gen), so
// rapid never enters a module's dependencies uninvited.

// genFieldExpr renders the generator expression for one field type.
func genFieldExpr(typeText string, siblings map[string]bool, qual string) string {
	switch typeText {
	case "int":
		return `rapid.Int().Draw(t, "f")`
	case "int64":
		return `rapid.Int64().Draw(t, "f")`
	case "string":
		return `rapid.String().Draw(t, "f")`
	case "bool":
		return `rapid.Bool().Draw(t, "f")`
	case "float64":
		return `rapid.Float64().Draw(t, "f")`
	}
	if siblings[typeText] {
		return "gen" + typeText + "Depth(t, depth-1)"
	}
	return fmt.Sprintf("rapid.Make[%s%s]().Draw(t, \"f\")", qualFor(typeText, qual), typeText)
}

func qualFor(typeText, qual string) string {
	if qual == "" || strings.Contains(typeText, ".") || isBuiltinType(typeText) {
		return ""
	}
	return qual
}

var builtinTypes = map[string]bool{
	"int": true, "int8": true, "int16": true, "int32": true, "int64": true,
	"uint": true, "uint8": true, "uint16": true, "uint32": true, "uint64": true,
	"string": true, "bool": true, "float32": true, "float64": true, "byte": true, "rune": true,
}

func isBuiltinType(t string) bool {
	return builtinTypes[strings.TrimLeft(t, "[]*")] && !strings.ContainsAny(t, "([{")
}

// enumWordRe matches whole-word identifiers for sibling detection.
func fieldMentionsSibling(typeText string, siblings map[string]bool) bool {
	for name := range siblings {
		if regexp.MustCompile(`\b` + regexp.QuoteMeta(name) + `\b`).MatchString(typeText) {
			return true
		}
	}
	return false
}

// RenderEnumGen renders Gen<Enum> and its depth helper. qual prefixes
// constructor and type references when the generator is emitted outside
// the enum's package ("" for same-package). ok is false when the enum
// cannot derive a generator (generic, indexed, or uninhabited at any
// depth).
func RenderEnumGen(e *registry.Enum, siblings map[string]bool, qual string) (string, bool) {
	if len(e.TParams) > 0 || len(e.Indices) > 0 {
		return "", false
	}
	// Leaves: variants with no sibling-enum fields.
	var leaves []int
	for i, v := range e.Variants {
		leaf := true
		for _, p := range v.Params {
			if fieldMentionsSibling(p.Type, siblings) {
				leaf = false
			}
		}
		if leaf {
			leaves = append(leaves, i)
		}
	}
	if len(leaves) == 0 {
		return "", false // uninhabited under any depth bound
	}

	var b strings.Builder
	name := e.Name
	fmt.Fprintf(&b, "// Gen%s draws a random %s (derived by goplus).\n", name, name)
	fmt.Fprintf(&b, "func Gen%s(t *rapid.T) %s%s {\n\treturn gen%sDepth(t, 3)\n}\n\n", name, qual, name, name)
	fmt.Fprintf(&b, "func gen%sDepth(t *rapid.T, depth int) %s%s {\n", name, qual, name)
	fmt.Fprintf(&b, "\tn := rapid.IntRange(0, %d).Draw(t, \"variant\")\n", len(e.Variants)-1)
	if len(leaves) < len(e.Variants) {
		leafList := make([]string, len(leaves))
		for i, li := range leaves {
			leafList[i] = fmt.Sprintf("%d", li)
		}
		fmt.Fprintf(&b, "\tif depth <= 0 {\n\t\tn = []int{%s}[rapid.IntRange(0, %d).Draw(t, \"leaf\")]\n\t}\n",
			strings.Join(leafList, ", "), len(leaves)-1)
	}
	b.WriteString("\tswitch n {\n")
	for i, v := range e.Variants {
		fmt.Fprintf(&b, "\tcase %d:\n", i)
		if !v.HasParams && len(v.Params) == 0 {
			// Bare variant: the erased constant/value or empty ctor.
			fmt.Fprintf(&b, "\t\treturn %s%s{}\n", qual, v.TypeName)
			continue
		}
		var fields []string
		for _, p := range v.Params {
			fields = append(fields, fmt.Sprintf("%s: %s", p.FieldName, genFieldExpr(p.Type, siblings, qual)))
		}
		fmt.Fprintf(&b, "\t\treturn %s%s{%s}\n", qual, v.TypeName, strings.Join(fields, ", "))
	}
	fmt.Fprintf(&b, "\t}\n\tpanic(\"goplus: impossible variant index in Gen%s\")\n}\n", name)
	return b.String(), true
}

// GenSiblings computes the derivable-enum name set for one package.
func GenSiblings(enums []*registry.Enum) map[string]bool {
	out := map[string]bool{}
	for _, e := range enums {
		if len(e.TParams) == 0 && len(e.Indices) == 0 {
			out[e.Name] = true
		}
	}
	return out
}

// planGenTests emits the opt-in generator test file for a package:
// enums marked //goplus:derive gen get their Gen<Enum> in a single
// <dir>/goplus_gen_test.go — a TEST file, so rapid stays a test-only
// concern and only for packages that asked.
func planGenTests(idx *pkgIndex, plan *enumPlan, pkgPath, dir string) (map[string][]byte, []diag.Diagnostic) {
	byName := map[string]*registry.Enum{}
	for _, m := range plan.models {
		byName[m.Name] = m
	}
	seedSet := map[string]bool{}
	for _, e := range plan.order {
		_, genOptIn, _ := deriveMode(e)
		if genOptIn {
			seedSet[plan.model[e].Name] = true
		}
	}
	if len(seedSet) == 0 {
		return nil, nil
	}
	var diags []diag.Diagnostic
	siblings := GenSiblings(plan.models)
	// Close over sibling references: Strategy's generator calls
	// genWhereDepth, so Where's generator must ride along.
	need := map[string]bool{}
	var frontier []string
	for n := range seedSet {
		need[n] = true
		frontier = append(frontier, n)
	}
	for len(frontier) > 0 {
		n := frontier[len(frontier)-1]
		frontier = frontier[:len(frontier)-1]
		e := byName[n]
		if e == nil {
			continue
		}
		for _, v := range e.Variants {
			for _, p := range v.Params {
				for sib := range siblings {
					if !need[sib] && fieldMentionsSibling(p.Type, map[string]bool{sib: true}) {
						need[sib] = true
						frontier = append(frontier, sib)
					}
				}
			}
		}
	}
	var opted []*registry.Enum
	for _, e := range plan.order {
		m := plan.model[e]
		if need[m.Name] {
			opted = append(opted, m)
		}
	}
	var b strings.Builder
	b.WriteString(emit.Header("derive-gen"))
	fmt.Fprintf(&b, "package %s\n\nimport \"pgregory.net/rapid\"\n", indexPkgName(idx))
	for _, e := range opted {
		text, ok := RenderEnumGen(e, siblings, "")
		if !ok {
			diags = append(diags, diag.Errorf("enum %s cannot derive a generator (type parameters, indices, or no leaf variant)", e.Name))
			continue
		}
		b.WriteString("\n" + text)
	}
	if len(diags) > 0 {
		return nil, diags
	}
	formatted, err := format.Source([]byte(b.String()))
	if err != nil {
		return nil, []diag.Diagnostic{diag.Errorf("internal error: formatting generators for %s: %v", pkgPath, err)}
	}
	return map[string][]byte{filepath.Join(dir, "goplus_gen_test.go"): formatted}, nil
}

// indexPkgName reads the package name from any parsed file.
func indexPkgName(idx *pkgIndex) string {
	for _, f := range idx.files {
		if f.ast != nil {
			return f.ast.Name.Name
		}
	}
	return "main"
}
