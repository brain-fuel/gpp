package gen

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/printer"
	"go/token"
	"strings"
	"unicode"
	"unicode/utf8"

	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/naming"
)

// Deep-traversal derivation (v0.11.0). Every SELF-RECURSIVE monomorphic
// enum derives, by default and alongside its fold:
//
//	func TmChildren(t Tm) []Tm            // direct same-enum subterms
//	func TmUniverse(t Tm) iter.Seq[Tm]    // t + transitive subterms, preorder
//	func TmTransform(t Tm, f func(Tm) Tm) Tm // bottom-up rewrite
//
// Names are always enum-prefixed. Descent sees through same-package
// struct wrappers whose fields (transitively) hold the enum — a binder
// wrapper like Scope{Name string; Body Tm} — and through slices of the
// enum or of wrappers. Generic and indexed enums, non-recursive enums,
// and `//gpp:derive off` enums derive nothing. Field shapes outside the
// descendable set are not descended: traversals cover the reachable
// enum spine.

// fieldShape classifies one field type for descent.
type fieldShape int

const (
	shapeNone         fieldShape = iota // not descended
	shapeEnum                           // E
	shapeSliceEnum                      // []E
	shapeWrapper                        // W, a same-package wrapper struct
	shapeSliceWrapper                   // []W
)

// wrapperDecl is one plain struct type declared in the package, a
// candidate descent wrapper.
type wrapperDecl struct {
	name   string
	fields []wrapperField // declaration order, flattened
}

type wrapperField struct {
	name string
	typ  string // canonical type text
}

// packageWrappers scans every package file for plain struct type
// declarations (embedded fields skipped — they have no selector path).
func packageWrappers(idx *pkgIndex) map[string]*wrapperDecl {
	out := map[string]*wrapperDecl{}
	for _, f := range idx.files {
		for _, decl := range f.ast.Decls {
			gd, ok := decl.(*ast.GenDecl)
			if !ok || gd.Tok != token.TYPE {
				continue
			}
			for _, s := range gd.Specs {
				ts, ok := s.(*ast.TypeSpec)
				if !ok || ts.TypeParams != nil {
					continue
				}
				st, ok := ts.Type.(*ast.StructType)
				if !ok {
					continue
				}
				w := &wrapperDecl{name: ts.Name.Name}
				for _, field := range st.Fields.List {
					text, err := typeText(field.Type)
					if err != nil {
						continue
					}
					for _, n := range field.Names {
						w.fields = append(w.fields, wrapperField{name: n.Name, typ: text})
					}
				}
				out[ts.Name.Name] = w
			}
		}
	}
	return out
}

func typeText(e ast.Expr) (string, error) {
	var buf bytes.Buffer
	if err := printer.Fprint(&buf, token.NewFileSet(), e); err != nil {
		return "", err
	}
	return buf.String(), nil
}

// enumWrappers computes the wrappers that (transitively) reach the enum
// through descendable shapes, then drops any wrapper on a wrapper-cycle
// (a self-recursive wrapper would need its own helper, not inline
// paths) and recomputes reachability over the survivors.
func enumWrappers(all map[string]*wrapperDecl, enumName string) map[string]*wrapperDecl {
	reach := map[string]bool{}
	for changed := true; changed; {
		changed = false
		for name, w := range all {
			if reach[name] {
				continue
			}
			for _, f := range w.fields {
				base := strings.TrimPrefix(f.typ, "[]")
				if base == enumName || reach[base] {
					reach[name] = true
					changed = true
					break
				}
			}
		}
	}
	// Drop cycle participants: a wrapper that can reach itself through
	// wrapper edges.
	const white, gray, black = 0, 1, 2
	color := map[string]int{}
	cyclic := map[string]bool{}
	var visit func(name string) bool // reports "on a cycle"
	visit = func(name string) bool {
		if color[name] == gray {
			return true
		}
		if color[name] == black {
			return cyclic[name]
		}
		color[name] = gray
		on := false
		for _, f := range all[name].fields {
			base := strings.TrimPrefix(f.typ, "[]")
			if reach[base] && visit(base) {
				on = true
			}
		}
		color[name] = black
		if on {
			cyclic[name] = true
		}
		return on
	}
	for name := range reach {
		visit(name)
	}
	for changed := true; changed; {
		changed = false
		for name := range reach {
			if cyclic[name] {
				delete(reach, name)
				changed = true
				continue
			}
			ok := false
			for _, f := range all[name].fields {
				base := strings.TrimPrefix(f.typ, "[]")
				if base == enumName || (reach[base] && !cyclic[base]) {
					ok = true
					break
				}
			}
			if !ok {
				delete(reach, name)
				changed = true
			}
		}
	}
	out := map[string]*wrapperDecl{}
	for name := range reach {
		out[name] = all[name]
	}
	return out
}

// classifyField assigns a descent shape to one field type text.
func classifyField(typ, enumName string, wrappers map[string]*wrapperDecl) fieldShape {
	typ = strings.TrimSpace(typ)
	if typ == enumName {
		return shapeEnum
	}
	if base, ok := strings.CutPrefix(typ, "[]"); ok {
		base = strings.TrimSpace(base)
		if base == enumName {
			return shapeSliceEnum
		}
		if _, isW := wrappers[base]; isW {
			return shapeSliceWrapper
		}
		return shapeNone
	}
	if _, isW := wrappers[typ]; isW {
		return shapeWrapper
	}
	return shapeNone
}

// planTraversals renders each qualifying enum's deep traversals into
// spec.TraversalText, reserving the three generated names.
func planTraversals(idx *pkgIndex, plan *enumPlan, tbl *naming.Table) []error {
	all := packageWrappers(idx)
	var errs []error
	for _, e := range plan.order {
		spec := plan.specs[e]
		model := plan.model[e]
		off, _, unknown := deriveMode(e)
		if off || unknown != "" { // unknown already reported by planFolds
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
		wrappers := enumWrappers(all, spec.Name)
		recursive := false
		for i := range spec.Variants {
			for _, fd := range spec.Variants[i].Fields {
				if classifyField(fd.Type, spec.Name, wrappers) != shapeNone {
					recursive = true
				}
			}
		}
		if !recursive {
			continue
		}
		childName := naming.PrefixedName(spec.Name, "Children")
		univName := naming.PrefixedName(spec.Name, "Universe")
		transName := naming.PrefixedName(spec.Name, "Transform")
		reserved := true
		for _, n := range []string{childName, univName, transName} {
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
		spec.TraversalText = renderTraversals(spec, wrappers, childName, univName, transName)
	}
	return errs
}

// traversalParamName picks the value parameter, avoiding the names the
// generated bodies use.
func traversalParamName(enumName string) string {
	r, _ := utf8.DecodeRuneInString(enumName)
	cand := string(unicode.ToLower(r))
	switch cand {
	case "f", "m", "c", "i", "w", "x", "s":
		return "t"
	}
	return cand
}

func renderTraversals(spec *lower.EnumSpec, wrappers map[string]*wrapperDecl, childName, univName, transName string) string {
	val := traversalParamName(spec.Name)
	var b strings.Builder
	n := 0 // loop-variable uniquifier across the whole render

	// Children.
	fmt.Fprintf(&b, "// %s lists the direct %s subterms of %s.\n", childName, spec.Name, val)
	fmt.Fprintf(&b, "func %s(%s %s) []%s {\n\tvar out []%s\n\tswitch m := any(%s).(type) {\n",
		childName, val, spec.Name, spec.Name, spec.Name, val)
	for i := range spec.Variants {
		vs := &spec.Variants[i]
		var stmts []string
		for _, fd := range vs.Fields {
			emitChildStmts(&stmts, "m."+fd.Name, fd.Type, spec.Name, wrappers, "\t\t", &n)
		}
		if len(stmts) == 0 {
			continue
		}
		fmt.Fprintf(&b, "\tcase %s:\n", vs.TypeName)
		for _, s := range stmts {
			b.WriteString(s)
		}
	}
	b.WriteString("\t}\n\treturn out\n}\n\n")

	// Universe.
	fmt.Fprintf(&b, "// %s yields %s and all transitive %s subterms, preorder.\n", univName, val, spec.Name)
	fmt.Fprintf(&b, "func %s(%s %s) iter.Seq[%s] {\n", univName, val, spec.Name, spec.Name)
	fmt.Fprintf(&b, "\treturn func(yield func(%s) bool) {\n", spec.Name)
	fmt.Fprintf(&b, "\t\tvar walk func(%s) bool\n", spec.Name)
	fmt.Fprintf(&b, "\t\twalk = func(cur %s) bool {\n", spec.Name)
	b.WriteString("\t\t\tif !yield(cur) {\n\t\t\t\treturn false\n\t\t\t}\n")
	fmt.Fprintf(&b, "\t\t\tfor _, c := range %s(cur) {\n", childName)
	b.WriteString("\t\t\t\tif !walk(c) {\n\t\t\t\t\treturn false\n\t\t\t\t}\n\t\t\t}\n\t\t\treturn true\n\t\t}\n")
	fmt.Fprintf(&b, "\t\twalk(%s)\n\t}\n}\n\n", val)

	// Transform.
	fmt.Fprintf(&b, "// %s rewrites %s bottom-up: children first, then f at each node.\n", transName, val)
	fmt.Fprintf(&b, "func %s(%s %s, f func(%s) %s) %s {\n\tswitch m := any(%s).(type) {\n",
		transName, val, spec.Name, spec.Name, spec.Name, spec.Name, val)
	for i := range spec.Variants {
		vs := &spec.Variants[i]
		var stmts []string
		for _, fd := range vs.Fields {
			emitTransformStmts(&stmts, "m."+fd.Name, fd.Type, spec.Name, transName, wrappers, "\t\t", &n)
		}
		if len(stmts) == 0 {
			continue
		}
		fmt.Fprintf(&b, "\tcase %s:\n", vs.TypeName)
		for _, s := range stmts {
			b.WriteString(s)
		}
		b.WriteString("\t\treturn f(m)\n")
	}
	fmt.Fprintf(&b, "\t}\n\treturn f(%s)\n}\n", val)
	return b.String()
}

// emitChildStmts appends the child-collection statements for one field
// expression of the given type.
func emitChildStmts(stmts *[]string, expr, typ, enumName string, wrappers map[string]*wrapperDecl, indent string, n *int) {
	switch classifyField(typ, enumName, wrappers) {
	case shapeEnum:
		// Guarded: erased enums are interfaces, and real code (an
		// optional annotation field) stores nil in them.
		*stmts = append(*stmts, fmt.Sprintf("%sif %s != nil {\n%s\tout = append(out, %s)\n%s}\n", indent, expr, indent, expr, indent))
	case shapeSliceEnum:
		loopVar := fmt.Sprintf("c%d", *n)
		*n++
		*stmts = append(*stmts, fmt.Sprintf("%sfor _, %s := range %s {\n", indent, loopVar, expr))
		*stmts = append(*stmts, fmt.Sprintf("%s\tif %s != nil {\n%s\t\tout = append(out, %s)\n%s\t}\n", indent, loopVar, indent, loopVar, indent))
		*stmts = append(*stmts, indent+"}\n")
	case shapeWrapper:
		w := wrappers[strings.TrimSpace(typ)]
		for _, fd := range w.fields {
			emitChildStmts(stmts, expr+"."+fd.name, fd.typ, enumName, wrappers, indent, n)
		}
	case shapeSliceWrapper:
		base := strings.TrimSpace(strings.TrimPrefix(strings.TrimSpace(typ), "[]"))
		w := wrappers[base]
		loopVar := fmt.Sprintf("w%d", *n)
		*n++
		var inner []string
		for _, fd := range w.fields {
			emitChildStmts(&inner, loopVar+"."+fd.name, fd.typ, enumName, wrappers, indent+"\t", n)
		}
		if len(inner) == 0 {
			return
		}
		*stmts = append(*stmts, fmt.Sprintf("%sfor _, %s := range %s {\n", indent, loopVar, expr))
		*stmts = append(*stmts, inner...)
		*stmts = append(*stmts, indent+"}\n")
	}
}

// emitTransformStmts appends the bottom-up rebuild statements for one
// assignable field expression of the given type. Slices are copied,
// never mutated in place.
func emitTransformStmts(stmts *[]string, lvalue, typ, enumName, transName string, wrappers map[string]*wrapperDecl, indent string, n *int) {
	switch classifyField(typ, enumName, wrappers) {
	case shapeEnum:
		// Guarded: a nil optional field passes through untouched; f
		// never sees nil.
		*stmts = append(*stmts, fmt.Sprintf("%sif %s != nil {\n%s\t%s = %s(%s, f)\n%s}\n", indent, lvalue, indent, lvalue, transName, lvalue, indent))
	case shapeSliceEnum:
		sliceVar := fmt.Sprintf("s%d", *n)
		idxVar := fmt.Sprintf("i%d", *n)
		elemVar := fmt.Sprintf("x%d", *n)
		*n++
		*stmts = append(*stmts, fmt.Sprintf("%sif len(%s) > 0 {\n", indent, lvalue))
		*stmts = append(*stmts, fmt.Sprintf("%s\t%s := make(%s, len(%s))\n", indent, sliceVar, strings.TrimSpace(typ), lvalue))
		*stmts = append(*stmts, fmt.Sprintf("%s\tfor %s, %s := range %s {\n", indent, idxVar, elemVar, lvalue))
		*stmts = append(*stmts, fmt.Sprintf("%s\t\t%s[%s] = %s\n", indent, sliceVar, idxVar, elemVar))
		*stmts = append(*stmts, fmt.Sprintf("%s\t\tif %s != nil {\n%s\t\t\t%s[%s] = %s(%s, f)\n%s\t\t}\n", indent, elemVar, indent, sliceVar, idxVar, transName, elemVar, indent))
		*stmts = append(*stmts, indent+"\t}\n")
		*stmts = append(*stmts, fmt.Sprintf("%s\t%s = %s\n", indent, lvalue, sliceVar))
		*stmts = append(*stmts, indent+"}\n")
	case shapeWrapper:
		w := wrappers[strings.TrimSpace(typ)]
		for _, fd := range w.fields {
			emitTransformStmts(stmts, lvalue+"."+fd.name, fd.typ, enumName, transName, wrappers, indent, n)
		}
	case shapeSliceWrapper:
		base := strings.TrimSpace(strings.TrimPrefix(strings.TrimSpace(typ), "[]"))
		w := wrappers[base]
		sliceVar := fmt.Sprintf("s%d", *n)
		idxVar := fmt.Sprintf("i%d", *n)
		*n++
		var inner []string
		for _, fd := range w.fields {
			emitTransformStmts(&inner, sliceVar+"["+idxVar+"]."+fd.name, fd.typ, enumName, transName, wrappers, indent+"\t\t", n)
		}
		if len(inner) == 0 {
			return
		}
		*stmts = append(*stmts, fmt.Sprintf("%sif len(%s) > 0 {\n", indent, lvalue))
		*stmts = append(*stmts, fmt.Sprintf("%s\t%s := make(%s, len(%s))\n", indent, sliceVar, strings.TrimSpace(typ), lvalue))
		*stmts = append(*stmts, fmt.Sprintf("%s\tcopy(%s, %s)\n", indent, sliceVar, lvalue))
		*stmts = append(*stmts, fmt.Sprintf("%s\tfor %s := range %s {\n", indent, idxVar, sliceVar))
		*stmts = append(*stmts, inner...)
		*stmts = append(*stmts, indent+"\t}\n")
		*stmts = append(*stmts, fmt.Sprintf("%s\t%s = %s\n", indent, lvalue, sliceVar))
		*stmts = append(*stmts, indent+"}\n")
	}
}
