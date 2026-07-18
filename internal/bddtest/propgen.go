package bddtest

import (
	"fmt"
	"go/format"
	"strings"

	"pgregory.net/rapid"
)

// Property-input generators. Everything generated here is valid by
// construction, so property failures always indicate a gpp defect, not a
// generator defect.

var (
	simpleTypes = []string{"int", "string", "bool", "[]int", "[]string", "map[string]int", "float64"}
	recvNames   = []string{"Stack", "Ring", "Box", "Tree", "bag", "heap"}
	docComments = []string{"", "// documented.\n", "// multi\n// line\n// docs.\n"}
)

// plainGoSource generates a small, gofmt-clean, self-contained Go file with
// no G++ constructs: declarations, comments, and simple bodies.
func plainGoSource(rt *rapid.T) string {
	var b strings.Builder
	n := rapid.IntRange(0, 9).Draw(rt, "pkgn")
	fmt.Fprintf(&b, "// Package p%d exercises passthrough.\npackage p%d\n\n", n, n)

	nDecls := rapid.IntRange(1, 5).Draw(rt, "ndecls")
	for i := 0; i < nDecls; i++ {
		t := rapid.SampledFrom(simpleTypes).Draw(rt, "type")
		doc := rapid.SampledFrom(docComments).Draw(rt, "doc")
		switch rapid.IntRange(0, 3).Draw(rt, "kind") {
		case 0:
			fmt.Fprintf(&b, "%stype Alias%d = %s\n\n", doc, i, t)
		case 1:
			fmt.Fprintf(&b, "%svar Value%d %s\n\n", doc, i, t)
		case 2:
			fmt.Fprintf(&b, "%sfunc Func%d(a %s) %s {\n\tvar z %s // inline comment\n\treturn z\n}\n\n", doc, i, t, t, t)
		default:
			fmt.Fprintf(&b, "%stype Struct%d struct {\n\tField %s\n}\n\nfunc (s Struct%d) Plain%d() %s {\n\treturn s.Field\n}\n\n",
				doc, i, t, i, i, t)
		}
	}
	src, err := format.Source([]byte(b.String()))
	if err != nil {
		rt.Fatalf("generator produced invalid Go (generator bug): %v\n%s", err, b.String())
	}
	return string(src)
}

// gppPackage is a generated G++ package as separable declaration blocks,
// so properties can permute declaration order.
type gppPackage struct {
	Header       string   // package clause + receiver type decl
	Decls        []string // remaining top-level blocks
	MethodNames  []string // expected lowered function names
	VariantNames []string // expected lowered variant struct names
}

func (p gppPackage) Source(order []int) string {
	var b strings.Builder
	b.WriteString(p.Header)
	if order == nil {
		for i := range p.Decls {
			b.WriteString(p.Decls[i])
		}
	} else {
		for _, i := range order {
			b.WriteString(p.Decls[i])
		}
	}
	return b.String()
}

// gppPackageGen generates a valid G++ package with 1..3 generic methods
// whose lowered names are collision-free by construction. The source is
// hand-formatted (gofmt cannot parse G++), matching gofmt conventions.
func gppPackageGen(rt *rapid.T) gppPackage {
	recv := rapid.SampledFrom(recvNames).Draw(rt, "recv")
	p := gppPackage{
		Header: fmt.Sprintf("package prop\n\ntype %s[T any] struct{ items []T }\n\n", recv),
	}

	nPlain := rapid.IntRange(0, 2).Draw(rt, "nplain")
	for i := 0; i < nPlain; i++ {
		t := rapid.SampledFrom(simpleTypes).Draw(rt, "ptype")
		p.Decls = append(p.Decls, fmt.Sprintf("func Helper%d(a %s) %s {\n\treturn a\n}\n\n", i, t, t))
	}

	// Optionally an enum: unique variant names avoid collision randomness
	// (collision behavior has its own scenarios).
	if rapid.Bool().Draw(rt, "hasenum") {
		enumName := rapid.SampledFrom([]string{"Signal", "Route", "state"}).Draw(rt, "ename")
		nVars := rapid.IntRange(1, 3).Draw(rt, "nvars")
		var b strings.Builder
		fmt.Fprintf(&b, "type %s[T any] enum {\n", enumName)
		for i := 0; i < nVars; i++ {
			vname := fmt.Sprintf("%s%d", rapid.SampledFrom([]string{"Go", "Stop", "wait"}).Draw(rt, "vname"), i)
			if rapid.Bool().Draw(rt, "vparams") {
				t := rapid.SampledFrom(simpleTypes).Draw(rt, "vtype")
				fmt.Fprintf(&b, "\t%s(payload %s, tag T)\n", vname, t)
			} else {
				fmt.Fprintf(&b, "\t%s\n", vname)
			}
			p.VariantNames = append(p.VariantNames, variantLoweredName(enumName, vname))
		}
		b.WriteString("}\n\n")
		p.Decls = append(p.Decls, b.String())
	}

	nMethods := rapid.IntRange(1, 3).Draw(rt, "nmethods")
	for i := 0; i < nMethods; i++ {
		ptr := ""
		if rapid.Bool().Draw(rt, "ptr") {
			ptr = "*"
		}
		doc := rapid.SampledFrom(docComments).Draw(rt, "mdoc")
		name := fmt.Sprintf("%s%d", rapid.SampledFrom([]string{"Map", "Walk", "fold"}).Draw(rt, "mname"), i)
		pt := rapid.SampledFrom(simpleTypes).Draw(rt, "mparam")
		p.Decls = append(p.Decls, fmt.Sprintf("%sfunc (r %s%s[T]) %s[U any](x %s, f func(T) U) []U {\n\t_ = x\n\treturn nil\n}\n\n",
			doc, ptr, recv, name, pt))
		p.MethodNames = append(p.MethodNames, loweredName(recv, name))
	}
	return p
}

// permutation draws a random ordering of n elements.
func permutation(rt *rapid.T, n int) []int {
	order := make([]int, n)
	for i := range order {
		order[i] = i
	}
	for i := n - 1; i > 0; i-- {
		j := rapid.IntRange(0, i).Draw(rt, "shuffle")
		order[i], order[j] = order[j], order[i]
	}
	return order
}

// variantLoweredName mirrors naming.VariantTypeName for package-unique
// variant names: the variant name itself, cased by combined visibility.
func variantLoweredName(enum, variant string) string {
	exported := enum[0] >= 'A' && enum[0] <= 'Z' && variant[0] >= 'A' && variant[0] <= 'Z'
	if exported {
		return strings.ToUpper(variant[:1]) + variant[1:]
	}
	return strings.ToLower(variant[:1]) + variant[1:]
}

func loweredName(recv, method string) string {
	exported := recv[0] >= 'A' && recv[0] <= 'Z' && method[0] >= 'A' && method[0] <= 'Z'
	first := strings.ToLower(recv[:1])
	if exported {
		first = strings.ToUpper(recv[:1])
	}
	return first + recv[1:] + strings.ToUpper(method[:1]) + method[1:]
}
