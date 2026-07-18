package registry

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"strings"

	"goforge.dev/gpp/internal/directive"
)

// EnumParam is one constructor parameter of a variant.
type EnumParam struct {
	Name      string // parameter name as written in G++, e.g. "value"
	FieldName string // Go struct field name, e.g. "Value"
	Type      string // type text in G++ terms, e.g. "T" or "func(T) U"
}

// EnumVariant is one variant of an enum.
type EnumVariant struct {
	Name       string      // G++ constructor name, e.g. "Some"
	TypeName   string      // lowered Go struct type name, e.g. "Some" or "OptionNone"
	Params     []EnumParam // nil for a bare variant
	HasParams  bool        // distinguishes None from None()
	ResultArgs []string    // GADT result type arguments; nil when defaulted
}

// Enum is a sealed sum type visible to a compilation.
type Enum struct {
	PkgPath  string
	Name     string   // enum (interface) type name
	TParams  []string // type parameter names
	Variants []*EnumVariant
}

// Origin renders a human-readable description for diagnostics.
func (e *Enum) Origin() string { return "enum " + e.Name }

// Variant finds a variant by its G++ constructor name.
func (e *Enum) Variant(name string) (*EnumVariant, bool) {
	for _, v := range e.Variants {
		if v.Name == name {
			return v, true
		}
	}
	return nil, false
}

// enum registry indexes, keyed like methods.
type enumIndex struct {
	byName        map[string]*Enum   // pkgPath \x00 enumName
	byVariantType map[string]*Enum   // pkgPath \x00 loweredTypeName
	byVariantName map[string][]*Enum // pkgPath \x00 gppVariantName
	variantNames  map[string]bool    // gpp variant names (candidate prefilter)
}

func (r *Registry) enums() *enumIndex {
	if r.enumIdx == nil {
		r.enumIdx = &enumIndex{
			byName:        map[string]*Enum{},
			byVariantType: map[string]*Enum{},
			byVariantName: map[string][]*Enum{},
			variantNames:  map[string]bool{},
		}
	}
	return r.enumIdx
}

// AddEnum registers an enum and its variants.
func (r *Registry) AddEnum(e *Enum) error {
	idx := r.enums()
	k := e.PkgPath + "\x00" + e.Name
	if _, exists := idx.byName[k]; exists {
		return fmt.Errorf("duplicate enum %s in package %s", e.Name, e.PkgPath)
	}
	idx.byName[k] = e
	for _, v := range e.Variants {
		idx.byVariantType[e.PkgPath+"\x00"+v.TypeName] = e
		vk := e.PkgPath + "\x00" + v.Name
		idx.byVariantName[vk] = append(idx.byVariantName[vk], e)
		idx.variantNames[v.Name] = true
	}
	return nil
}

// LookupEnum finds an enum by its interface type name.
func (r *Registry) LookupEnum(pkgPath, name string) (*Enum, bool) {
	e, ok := r.enums().byName[pkgPath+"\x00"+name]
	return e, ok
}

// EnumByVariantType finds the enum declaring a lowered variant struct.
func (r *Registry) EnumByVariantType(pkgPath, typeName string) (*Enum, bool) {
	e, ok := r.enums().byVariantType[pkgPath+"\x00"+typeName]
	return e, ok
}

// EnumsByVariantName lists the enums of a package declaring a variant with
// this G++ name (>1 means bare references are ambiguous without inference).
func (r *Registry) EnumsByVariantName(pkgPath, name string) []*Enum {
	return r.enums().byVariantName[pkgPath+"\x00"+name]
}

// HasVariantName reports whether any registered enum declares this variant
// name — a cheap candidate prefilter.
func (r *Registry) HasVariantName(name string) bool { return r.enums().variantNames[name] }

// AllEnums returns registered enums in deterministic order.
func (r *Registry) AllEnums() []*Enum {
	idx := r.enums()
	keys := make([]string, 0, len(idx.byName))
	for k := range idx.byName {
		keys = append(keys, k)
	}
	sortStrings(keys)
	out := make([]*Enum, 0, len(keys))
	for _, k := range keys {
		out = append(out, idx.byName[k])
	}
	return out
}

// EnumsFromMarkers scans a dependency's distributed Go source for
// //gpp:enum and //gpp:variant markers, reconstructing the enum model.
// Tolerant: damaged markers make an enum invisible, never fatal.
func EnumsFromMarkers(pkgPath, filename string, src []byte) ([]*Enum, error) {
	if !strings.Contains(string(src), "//gpp:enum") {
		return nil, nil
	}
	fset := token.NewFileSet()
	astFile, err := parser.ParseFile(fset, filename, src, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		return nil, fmt.Errorf("parsing %s for gpp markers: %w", filename, err)
	}
	enums := map[string]*Enum{}
	var order []string

	// First pass: //gpp:enum markers on interface type decls.
	for _, decl := range astFile.Decls {
		gd, ok := decl.(*ast.GenDecl)
		if !ok || gd.Tok != token.TYPE {
			continue
		}
		for _, c := range docLines(gd.Doc) {
			if m, ok := directive.ParseEnumMarker(c); ok {
				e := &Enum{PkgPath: pkgPath, Name: m.Name, TParams: tparamNames(m.TParams)}
				enums[m.Name] = e
				order = append(order, m.Name)
			}
		}
	}
	// Second pass: //gpp:variant markers on struct type decls, paired with
	// the decl to learn the lowered type name and Go field names.
	for _, decl := range astFile.Decls {
		gd, ok := decl.(*ast.GenDecl)
		if !ok || gd.Tok != token.TYPE || len(gd.Specs) != 1 {
			continue
		}
		ts, ok := gd.Specs[0].(*ast.TypeSpec)
		if !ok {
			continue
		}
		st, ok := ts.Type.(*ast.StructType)
		if !ok {
			continue
		}
		for _, c := range docLines(gd.Doc) {
			m, ok := directive.ParseVariantMarker(c)
			if !ok {
				continue
			}
			e, ok := enums[m.EnumName]
			if !ok {
				continue
			}
			v := &EnumVariant{Name: m.Name, TypeName: ts.Name.Name, HasParams: m.HasParams}
			if m.Result != "" {
				v.ResultArgs = resultArgsOf(m.Result)
			}
			params := parseParamList(m.Params)
			fields := flattenFields(st)
			for i, p := range params {
				fieldName := p.Name
				if i < len(fields) {
					fieldName = fields[i]
				}
				v.Params = append(v.Params, EnumParam{Name: p.Name, FieldName: fieldName, Type: p.Type})
			}
			e.Variants = append(e.Variants, v)
			break
		}
	}
	var out []*Enum
	for _, name := range order {
		if len(enums[name].Variants) > 0 {
			out = append(out, enums[name])
		}
	}
	return out, nil
}

func docLines(doc *ast.CommentGroup) []string {
	if doc == nil {
		return nil
	}
	out := make([]string, len(doc.List))
	for i, c := range doc.List {
		out[i] = c.Text
	}
	return out
}

func tparamNames(tparams string) []string {
	if strings.TrimSpace(tparams) == "" {
		return nil
	}
	// "T any" / "K comparable, V any" / grouped "K, V any"
	var names []string
	for _, group := range splitTopLevel(tparams, ',') {
		fieldsOf := strings.Fields(strings.TrimSpace(group))
		if len(fieldsOf) > 0 {
			names = append(names, strings.TrimSuffix(fieldsOf[0], ","))
		}
	}
	return names
}

// paramDecl is a (name, type) pair parsed from a marker's param list.
type paramDecl struct{ Name, Type string }

// parseParamList parses "value T" / "w, h float64" / "f func(T) U, n int"
// into flattened (name, type) pairs.
func parseParamList(params string) []paramDecl {
	params = strings.TrimSpace(params)
	if params == "" {
		return nil
	}
	var out []paramDecl
	var pendingNames []string
	for _, part := range splitTopLevel(params, ',') {
		part = strings.TrimSpace(part)
		if i := strings.IndexAny(part, " \t"); i > 0 && !strings.ContainsAny(part[:i], "([*") {
			name := part[:i]
			typ := strings.TrimSpace(part[i+1:])
			for _, pn := range pendingNames {
				out = append(out, paramDecl{Name: pn, Type: typ})
			}
			pendingNames = nil
			out = append(out, paramDecl{Name: name, Type: typ})
		} else {
			// A bare name awaiting a shared type: "w" in "w, h float64".
			pendingNames = append(pendingNames, part)
		}
	}
	return out
}

// splitTopLevel splits on sep outside any bracket nesting.
func splitTopLevel(s string, sep rune) []string {
	var out []string
	depth := 0
	start := 0
	for i, r := range s {
		switch r {
		case '(', '[', '{':
			depth++
		case ')', ']', '}':
			depth--
		case sep:
			if depth == 0 {
				out = append(out, s[start:i])
				start = i + 1
			}
		}
	}
	out = append(out, s[start:])
	return out
}

// resultArgsOf extracts the argument texts of "Expr[int]" → ["int"].
func resultArgsOf(result string) []string {
	open := strings.Index(result, "[")
	if open < 0 || !strings.HasSuffix(result, "]") {
		return []string{}
	}
	var out []string
	for _, a := range splitTopLevel(result[open+1:len(result)-1], ',') {
		out = append(out, strings.TrimSpace(a))
	}
	return out
}

// flattenFields lists a struct's field names in declaration order.
func flattenFields(st *ast.StructType) []string {
	var out []string
	for _, f := range st.Fields.List {
		for _, n := range f.Names {
			out = append(out, n.Name)
		}
	}
	return out
}

func sortStrings(s []string) {
	for i := 1; i < len(s); i++ {
		for j := i; j > 0 && s[j] < s[j-1]; j-- {
			s[j], s[j-1] = s[j-1], s[j]
		}
	}
}
