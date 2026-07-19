package gen

import (
	"fmt"
	"strings"

	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/naming"
)

// Structural-equality derivation (v0.11.0). Every monomorphic enum
// derives, by default:
//
//	func TmEqual(a, b Tm) bool
//	func TmEqualWith(a, b Tm, ov TmEqOverrides) bool
//	type TmEqOverrides struct { Cast func(x, y Cast) (eq, handled bool); … }
//
// Comparison is variant-wise and field-wise, recursive through fields
// of the enum itself, same-package descent wrappers, slices of either,
// and fields typed as OTHER derivable same-package enums (via their
// plain <Enum>Equal — overrides do not cross enums). An override hook
// returning handled=false falls through to the derived comparison.
// Underivable — silently, no error: enums with func-, map-, or
// chan-typed content in the reachable spine, fields typed as
// underivable enums (transitively), fields typed as same-package
// structs that are not comparable, generic or indexed enums, and
// `//gpp:derive off`.

// eqShape classifies one field type for equality descent.
type eqShape int

const (
	eqOpaque       eqShape = iota // compare with ==
	eqSelf                        // the deriving enum
	eqSliceSelf                   // []E
	eqWrapper                     // descent wrapper of E
	eqSliceWrapper                // []W
	eqOtherEnum                   // another same-package derivable enum
	eqSliceOther                  // slice of same
	eqSliceOpaque                 // slice of opaque comparable elements
	eqBad                         // underivable content
)

// eqEnv is the package-level context equality derivation runs in.
type eqEnv struct {
	enumName  string                  // the deriving enum
	wrappers  map[string]*wrapperDecl // descent wrappers of enumName
	enums     map[string]bool         // ALL package enum names
	derivable map[string]bool         // current fixpoint estimate
	structs   map[string]*wrapperDecl // all package structs
}

func badTypeText(typ string) bool {
	return strings.Contains(typ, "func(") || strings.Contains(typ, "func ") ||
		strings.Contains(typ, "map[") || strings.Contains(typ, "chan ") ||
		strings.HasSuffix(typ, "chan") || strings.Contains(typ, "chan<-")
}

// structComparable reports whether == compiles for a same-package
// struct: no func/map/chan/slice content, transitively. Unknown
// (imported) field types are assumed comparable.
func structComparable(name string, structs map[string]*wrapperDecl, seen map[string]bool) bool {
	if seen[name] {
		return true // cycle: optimistic; the cycle itself has no bad content
	}
	seen[name] = true
	w, ok := structs[name]
	if !ok {
		return true
	}
	for _, f := range w.fields {
		if badTypeText(f.typ) || strings.HasPrefix(strings.TrimSpace(f.typ), "[]") {
			return false
		}
		base := strings.TrimSpace(f.typ)
		if _, isStruct := structs[base]; isStruct && !structComparable(base, structs, seen) {
			return false
		}
	}
	return true
}

// classifyEq assigns an equality shape to one field type text.
func classifyEq(typ string, env *eqEnv) eqShape {
	typ = strings.TrimSpace(typ)
	if badTypeText(typ) {
		return eqBad
	}
	if typ == env.enumName {
		return eqSelf
	}
	if base, ok := strings.CutPrefix(typ, "[]"); ok {
		base = strings.TrimSpace(base)
		if badTypeText(base) {
			return eqBad
		}
		if base == env.enumName {
			return eqSliceSelf
		}
		if _, isW := env.wrappers[base]; isW {
			return eqSliceWrapper
		}
		if env.enums[base] {
			if !env.derivable[base] {
				return eqBad
			}
			return eqSliceOther
		}
		if _, isStruct := env.structs[base]; isStruct && !structComparable(base, env.structs, map[string]bool{}) {
			return eqBad
		}
		if strings.HasPrefix(base, "[]") {
			return eqBad // nested slices: elements are not comparable
		}
		return eqSliceOpaque
	}
	if _, isW := env.wrappers[typ]; isW {
		return eqWrapper
	}
	if env.enums[typ] {
		if !env.derivable[typ] {
			return eqBad
		}
		return eqOtherEnum
	}
	if _, isStruct := env.structs[typ]; isStruct && !structComparable(typ, env.structs, map[string]bool{}) {
		return eqBad
	}
	return eqOpaque
}

// enumEqDerivable checks every reachable field of the enum, descending
// wrappers.
func enumEqDerivable(spec *lower.EnumSpec, env *eqEnv) bool {
	var fieldsOK func(typ string, seen map[string]bool) bool
	fieldsOK = func(typ string, seen map[string]bool) bool {
		switch classifyEq(typ, env) {
		case eqBad:
			return false
		case eqWrapper, eqSliceWrapper:
			base := strings.TrimSpace(strings.TrimPrefix(strings.TrimSpace(typ), "[]"))
			if seen[base] {
				return true
			}
			seen[base] = true
			for _, f := range env.wrappers[base].fields {
				if !fieldsOK(f.typ, seen) {
					return false
				}
			}
		}
		return true
	}
	for i := range spec.Variants {
		for _, fd := range spec.Variants[i].Fields {
			if !fieldsOK(fd.Type, map[string]bool{}) {
				return false
			}
		}
	}
	return true
}

// planEquality renders each qualifying enum's structural equality into
// spec.EqualText, reserving the three generated names. Derivability is
// a fixpoint: an enum referencing an underivable enum is underivable.
func planEquality(idx *pkgIndex, plan *enumPlan, tbl *naming.Table) []error {
	all := packageWrappers(idx)
	enumNames := map[string]bool{}
	for _, m := range plan.models {
		enumNames[m.Name] = true
	}

	candidates := map[string]*lower.EnumSpec{}
	derivable := map[string]bool{}
	for _, e := range plan.order {
		spec := plan.specs[e]
		model := plan.model[e]
		off, _, unknown := deriveMode(e)
		if off || unknown != "" {
			continue
		}
		if spec.TParamsSrc != "" || (model != nil && len(model.Indices) > 0) {
			continue
		}
		variantTP := false
		for i := range spec.Variants {
			if len(spec.Variants[i].TParamNames) > 0 {
				variantTP = true
			}
		}
		if variantTP {
			continue
		}
		candidates[spec.Name] = spec
		derivable[spec.Name] = true
	}

	envOf := func(name string) *eqEnv {
		return &eqEnv{
			enumName:  name,
			wrappers:  enumWrappers(all, name),
			enums:     enumNames,
			derivable: derivable,
			structs:   all,
		}
	}
	for changed := true; changed; {
		changed = false
		for name, spec := range candidates {
			if !derivable[name] {
				continue
			}
			if !enumEqDerivable(spec, envOf(name)) {
				derivable[name] = false
				changed = true
			}
		}
	}

	var errs []error
	for _, e := range plan.order {
		spec := plan.specs[e]
		if !derivable[spec.Name] || candidates[spec.Name] != spec {
			continue
		}
		env := envOf(spec.Name)
		eqName := naming.PrefixedName(spec.Name, "Equal")
		withName := naming.PrefixedName(spec.Name, "EqualWith")
		ovName := naming.PrefixedName(spec.Name, "EqOverrides")
		reserved := true
		for _, n := range []string{eqName, withName, ovName} {
			origin := fmt.Sprintf("derived %s for enum %s at %s", n, spec.Name, idx.fset.Position(e.Spec.Pos()))
			if err := tbl.AddGenerated(n, origin); err != nil {
				errs = append(errs, err)
				reserved = false
				break
			}
		}
		if !reserved {
			continue
		}
		spec.EqualText = renderEquality(spec, env, eqName, withName, ovName)
	}
	return errs
}

func renderEquality(spec *lower.EnumSpec, env *eqEnv, eqName, withName, ovName string) string {
	var b strings.Builder
	n := 0

	// Overrides struct.
	fmt.Fprintf(&b, "// %s carries optional per-variant hooks for %s.\n", ovName, withName)
	b.WriteString("// A hook returning handled=false falls through to the derived comparison.\n")
	fmt.Fprintf(&b, "type %s struct {\n", ovName)
	for i := range spec.Variants {
		vs := &spec.Variants[i]
		fmt.Fprintf(&b, "\t%s func(x, y %s) (eq, handled bool)\n", vs.GppName, vs.TypeName)
	}
	b.WriteString("}\n\n")

	// EqualWith.
	fmt.Fprintf(&b, "// %s reports structural equality of a and b under ov.\n", withName)
	fmt.Fprintf(&b, "func %s(a, b %s, ov %s) bool {\n", withName, spec.Name, ovName)
	b.WriteString("\tif a == nil || b == nil {\n\t\treturn a == nil && b == nil\n\t}\n")
	b.WriteString("\tswitch x := any(a).(type) {\n")
	for i := range spec.Variants {
		vs := &spec.Variants[i]
		fmt.Fprintf(&b, "\tcase %s:\n", vs.TypeName)
		fmt.Fprintf(&b, "\t\ty, ok := any(b).(%s)\n\t\tif !ok {\n\t\t\treturn false\n\t\t}\n", vs.TypeName)
		fmt.Fprintf(&b, "\t\tif ov.%s != nil {\n", vs.GppName)
		fmt.Fprintf(&b, "\t\t\tif eq, handled := ov.%s(x, y); handled {\n\t\t\t\treturn eq\n\t\t\t}\n\t\t}\n", vs.GppName)
		if len(vs.Fields) == 0 {
			b.WriteString("\t\t_ = y\n")
		}
		for _, fd := range vs.Fields {
			emitEqStmts(&b, "x."+fd.Name, "y."+fd.Name, fd.Type, env, withName, "\t\t", &n)
		}
		b.WriteString("\t\treturn true\n")
	}
	b.WriteString("\t}\n\treturn false\n}\n\n")

	// Equal.
	fmt.Fprintf(&b, "// %s reports structural equality of a and b.\n", eqName)
	fmt.Fprintf(&b, "func %s(a, b %s) bool {\n\treturn %s(a, b, %s{})\n}\n", eqName, spec.Name, withName, ovName)
	return b.String()
}

// emitEqStmts writes the comparison statements for one field pair.
func emitEqStmts(b *strings.Builder, xe, ye, typ string, env *eqEnv, withName, indent string, n *int) {
	typ = strings.TrimSpace(typ)
	switch classifyEq(typ, env) {
	case eqSelf:
		fmt.Fprintf(b, "%sif !%s(%s, %s, ov) {\n%s\treturn false\n%s}\n", indent, withName, xe, ye, indent, indent)
	case eqOtherEnum:
		other := naming.PrefixedName(typ, "Equal")
		fmt.Fprintf(b, "%sif !%s(%s, %s) {\n%s\treturn false\n%s}\n", indent, other, xe, ye, indent, indent)
	case eqSliceSelf, eqSliceOther, eqSliceOpaque:
		base := strings.TrimSpace(strings.TrimPrefix(typ, "[]"))
		iv := fmt.Sprintf("i%d", *n)
		*n++
		fmt.Fprintf(b, "%sif len(%s) != len(%s) {\n%s\treturn false\n%s}\n", indent, xe, ye, indent, indent)
		fmt.Fprintf(b, "%sfor %s := range %s {\n", indent, iv, xe)
		switch classifyEq(typ, env) {
		case eqSliceSelf:
			fmt.Fprintf(b, "%s\tif !%s(%s[%s], %s[%s], ov) {\n%s\t\treturn false\n%s\t}\n", indent, withName, xe, iv, ye, iv, indent, indent)
		case eqSliceOther:
			other := naming.PrefixedName(base, "Equal")
			fmt.Fprintf(b, "%s\tif !%s(%s[%s], %s[%s]) {\n%s\t\treturn false\n%s\t}\n", indent, other, xe, iv, ye, iv, indent, indent)
		default:
			fmt.Fprintf(b, "%s\tif %s[%s] != %s[%s] {\n%s\t\treturn false\n%s\t}\n", indent, xe, iv, ye, iv, indent, indent)
		}
		fmt.Fprintf(b, "%s}\n", indent)
	case eqWrapper:
		for _, fd := range env.wrappers[typ].fields {
			emitEqStmts(b, xe+"."+fd.name, ye+"."+fd.name, fd.typ, env, withName, indent, n)
		}
	case eqSliceWrapper:
		base := strings.TrimSpace(strings.TrimPrefix(typ, "[]"))
		iv := fmt.Sprintf("i%d", *n)
		*n++
		fmt.Fprintf(b, "%sif len(%s) != len(%s) {\n%s\treturn false\n%s}\n", indent, xe, ye, indent, indent)
		fmt.Fprintf(b, "%sfor %s := range %s {\n", indent, iv, xe)
		for _, fd := range env.wrappers[base].fields {
			emitEqStmts(b, xe+"["+iv+"]."+fd.name, ye+"["+iv+"]."+fd.name, fd.typ, env, withName, indent+"\t", n)
		}
		fmt.Fprintf(b, "%s}\n", indent)
	default: // eqOpaque
		fmt.Fprintf(b, "%sif %s != %s {\n%s\treturn false\n%s}\n", indent, xe, ye, indent, indent)
	}
}
