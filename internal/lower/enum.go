package lower

import (
	"fmt"
	"strings"

	"goforge.dev/gpp/internal/syntax"
)

// EnumSpec is a fully-resolved enum ready to render: names assigned,
// GADT result types analyzed, field types substituted. Computed by gen.
type EnumSpec struct {
	Name        string // enum (interface) type name
	TParamsSrc  string // full tparam list with constraints, e.g. "T any"; ""
	TParamNames []string
	MarkerName  string // sealed marker method, e.g. "isOption"
	EnumMarker  string // "//gpp:enum Option[T any]"
	Variants    []EnumVariantSpec
	FoldText    string // derived Cases struct + Fold function (v0.6.0); "" = none
	TraversalText string // derived Children/Universe/Transform (v0.11.0); "" = none
	EqualText     string // derived Equal/EqualWith/EqOverrides (v0.11.0); "" = none
}

// EnumVariantSpec is one variant ready to render.
type EnumVariantSpec struct {
	GppName     string   // constructor name as written, e.g. "Some"
	TypeName    string   // lowered struct name
	TParamsSrc  string   // kept tparams with constraints; "" for ground variants
	TParamNames []string // kept tparam names
	MarkerArgs  []string // sealed-method parameter types (result type args)
	Fields      []FieldSpec
	ParamNames  []string // original parameter names, aligned with Fields
	Marker      string   // "//gpp:variant (Option[T]) Some(value T)"
}

// FieldSpec is one struct field of a variant.
type FieldSpec struct {
	Name string
	Type string
}

// EnumEdits lowers one enum declaration: a marker line above the decl and
// a single replacement of the `type X enum { … }` span with the sealed
// interface, variant structs, and marker methods.
func EnumEdits(f *syntax.File, e *syntax.EnumDecl, spec *EnumSpec) []Edit {
	declStart := f.Offset(e.Gen.Pos())
	declEnd := f.Offset(e.Gen.End())

	var edits []Edit
	// //gpp:enum marker above the declaration (above its doc comment;
	// gofmt canonicalizes directive placement).
	markerAt := declStart
	if e.Gen.Doc != nil {
		markerAt = f.Offset(e.Gen.Doc.Pos())
	}
	for markerAt > 0 && f.Src[markerAt-1] != '\n' {
		markerAt--
	}
	edits = append(edits, Edit{Start: markerAt, End: markerAt, New: spec.EnumMarker + "\n"})

	var b strings.Builder
	// Sealed interface.
	fmt.Fprintf(&b, "type %s%s interface{ %s(%s) }\n",
		spec.Name, bracket(spec.TParamsSrc), spec.MarkerName, strings.Join(spec.TParamNames, ", "))

	for _, v := range spec.Variants {
		b.WriteString("\n")
		b.WriteString(v.Marker + "\n")
		if len(v.Fields) == 0 {
			fmt.Fprintf(&b, "type %s%s struct{}\n", v.TypeName, bracket(v.TParamsSrc))
		} else {
			fmt.Fprintf(&b, "type %s%s struct {\n", v.TypeName, bracket(v.TParamsSrc))
			for _, fd := range v.Fields {
				fmt.Fprintf(&b, "\t%s %s\n", fd.Name, fd.Type)
			}
			b.WriteString("}\n")
		}
		fmt.Fprintf(&b, "\nfunc (%s%s) %s(%s) {}\n",
			v.TypeName, bracket(strings.Join(v.TParamNames, ", ")), spec.MarkerName, strings.Join(v.MarkerArgs, ", "))
	}

	if spec.FoldText != "" {
		b.WriteString("\n" + spec.FoldText)
	}
	if spec.TraversalText != "" {
		b.WriteString("\n" + spec.TraversalText)
	}
	if spec.EqualText != "" {
		b.WriteString("\n" + spec.EqualText)
	}
	edits = append(edits, Edit{Start: declStart, End: declEnd, New: strings.TrimSuffix(b.String(), "\n")})
	return edits
}

func bracket(inner string) string {
	if inner == "" {
		return ""
	}
	return "[" + inner + "]"
}
