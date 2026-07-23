package registry

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"regexp"
	"sort"
	"strings"

	"goforge.dev/goplus/internal/directive"
)

// EnumParam is one constructor parameter of a variant.
type EnumParam struct {
	Name      string // parameter name as written in Go+, e.g. "value"
	FieldName string // Go struct field name, e.g. "Value"
	Type      string // ERASED type text, e.g. "T" or "Vec[T]"
	RawType   string // unerased type text ("Vec[T, n]"); == Type without indices
}

// EnumVariant is one variant of an enum.
type EnumVariant struct {
	// Occurs lists the enum type parameters (indices) appearing anywhere
	// in the variant's result arguments — the struct's type parameters.
	// nil ResultArgs (defaulted result) means all.
	Occurs []int

	Name       string      // Go+ constructor name, e.g. "Some"
	TypeName   string      // lowered Go struct type name, e.g. "Some" or "OptionNone"
	Params     []EnumParam // nil for a bare variant; types ERASED for existentials
	HasParams  bool        // distinguishes None from None()
	ResultArgs []string    // ERASED GADT result type arguments; nil when defaulted
	IndexArgs  []string    // index-position result terms, in Indices order (v0.7.0)
	Exist      []ExistTP   // bounded existential tparams (v0.6.0); nil otherwise
}

// OccursIn returns the variant's occurring enum-tparam indices,
// computing them from ResultArgs texts when unset (marker-reconstructed
// variants). A defaulted result means every parameter occurs.
func (v *EnumVariant) OccursIn(e *Enum) []int {
	if v.ResultArgs == nil {
		out := make([]int, len(e.TParams))
		for i := range out {
			out[i] = i
		}
		return out
	}
	if v.Occurs != nil {
		return v.Occurs
	}
	occursSet := map[int]bool{}
	idx := map[string]int{}
	for i, n := range e.TParams {
		idx[n] = i
	}
	for _, arg := range v.ResultArgs {
		expr, err := parser.ParseExpr(arg)
		if err != nil {
			continue
		}
		for _, name := range typeIdentNames(expr) {
			if i, isTP := idx[name]; isTP {
				occursSet[i] = true
			}
		}
	}
	var out []int
	for i := range e.TParams {
		if occursSet[i] {
			out = append(out, i)
		}
	}
	v.Occurs = out
	return out
}

// typeIdentNames lists identifier names free in a type expression
// (selector .Sel skipped).
func typeIdentNames(e ast.Expr) []string {
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

// Enum is a sealed sum type visible to a compilation.
type Enum struct {
	PkgPath  string
	Name     string        // enum (interface) type name
	TParams  []string      // ERASED type parameter names
	Indices  []IndexBinder // value-index binders (v0.7.0); nil otherwise
	IsDomain bool          // usable as a first-order index domain (v0.9.0)
	Variants []*EnumVariant
}

// DomainTags returns tag name → arity for a domain enum.
func (e *Enum) DomainTags() map[string]int {
	out := map[string]int{}
	for _, v := range e.Variants {
		out[v.Name] = len(v.Params)
	}
	return out
}

// Origin renders a human-readable description for diagnostics.
func (e *Enum) Origin() string { return "enum " + e.Name }

// Variant finds a variant by its Go+ constructor name.
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
	byVariantName map[string][]*Enum // pkgPath \x00 goplusVariantName
	variantNames  map[string]bool    // goplus variant names (candidate prefilter)
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
// this Go+ name (>1 means bare references are ambiguous without inference).
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

// EnumsFromMarkers reconstructs the enum model from one file — a thin
// wrapper over the package-level reconstruction.
func EnumsFromMarkers(pkgPath, filename string, src []byte) ([]*Enum, error) {
	return EnumsFromPackageMarkers(pkgPath, map[string][]byte{filename: src}, nil)
}

// ExternDomain looks up a possibly-imported enum for domain checks
// during reconstruction (the registry, in dependency-first order).
type ExternDomain func(importPath, name string) (*Enum, bool)

// EnumsFromPackageMarkers scans a dependency PACKAGE's distributed Go
// sources for //goplus:enum and //goplus:variant markers, reconstructing the
// enum model with cross-file knowledge: an enum may reference an index
// domain or another indexed enum declared in a sibling file. Tolerant:
// damaged markers make an enum invisible, never fatal.
func EnumsFromPackageMarkers(pkgPath string, files map[string][]byte, extern ExternDomain) ([]*Enum, error) {
	type parsedFile struct {
		name string
		file *ast.File
	}
	var parsed []parsedFile
	fset := token.NewFileSet()
	names := make([]string, 0, len(files))
	for name := range files {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		src := files[name]
		if !strings.Contains(string(src), "//goplus:enum") {
			continue
		}
		astFile, err := parser.ParseFile(fset, name, src, parser.ParseComments|parser.SkipObjectResolution)
		if err != nil {
			return nil, fmt.Errorf("parsing %s for goplus markers: %w", name, err)
		}
		parsed = append(parsed, parsedFile{name: name, file: astFile})
	}
	if len(parsed) == 0 {
		return nil, nil
	}
	enums := map[string]*Enum{}
	var order []string

	// First pass: //goplus:enum markers on interface type decls. Binder
	// partition happens after ALL markers are gathered — an index-domain
	// enum (zero tparams) may be declared later in the file than the
	// enum indexed over it.
	rawTParams := map[string]string{}
	declFile := map[string]*ast.File{}
	for _, pf := range parsed {
		for _, decl := range pf.file.Decls {
			gd, ok := decl.(*ast.GenDecl)
			if !ok || gd.Tok != token.TYPE {
				continue
			}
			for _, c := range docLines(gd.Doc) {
				if m, ok := directive.ParseEnumMarker(c); ok {
					e := &Enum{PkgPath: pkgPath, Name: m.Name}
					rawTParams[m.Name] = m.TParams
					declFile[m.Name] = pf.file
					enums[m.Name] = e
					order = append(order, m.Name)
				}
			}
		}
	}
	// Index domains mirror gen's rule: a zero-tparam enum whose variant
	// parameters are all index-sorted (nat or another domain), with no
	// variant tparams or results — computed by fixpoint from the raw
	// variant markers before binder partition. A field may recursively carry
	// its own domain, enabling strictly-positive type-level lists.
	type rawVariant struct {
		enum string
		m    directive.VariantMarker
	}
	var rawVariants []rawVariant
	for _, pf := range parsed {
		for _, decl := range pf.file.Decls {
			gd, ok := decl.(*ast.GenDecl)
			if !ok || gd.Tok != token.TYPE || len(gd.Specs) != 1 {
				continue
			}
			for _, c := range docLines(gd.Doc) {
				if m, ok := directive.ParseVariantMarker(c); ok {
					rawVariants = append(rawVariants, rawVariant{enum: m.EnumName, m: m})
				}
			}
		}
	}
	domains := map[string]bool{}
	for changed := true; changed; {
		changed = false
		for name := range enums {
			if domains[name] || strings.TrimSpace(rawTParams[name]) != "" {
				continue
			}
			okDomain, seen := true, false
			for _, rv := range rawVariants {
				if rv.enum != name {
					continue
				}
				seen = true
				if rv.m.TParams != "" || rv.m.Result != "" {
					okDomain = false
					break
				}
				for _, p := range parseParamList(rv.m.Params) {
					if p.Type != "nat" && p.Type != name && !domains[p.Type] {
						okDomain = false
					}
				}
				if !okDomain {
					break
				}
			}
			if okDomain && seen {
				domains[name] = true
				changed = true
			}
		}
	}
	for name, e := range enums {
		e.IsDomain = domains[name]
	}
	for name, e := range enums {
		file := declFile[name]
		isDomain := func(ctext string) (string, bool) {
			if domains[ctext] {
				return "", true
			}
			// Qualified constraint: resolve the alias through the
			// DECLARING file's imports and ask the registry.
			if i := strings.LastIndex(ctext, "."); i > 0 && extern != nil && file != nil {
				alias, base := ctext[:i], ctext[i+1:]
				for _, imp := range file.Imports {
					path := strings.Trim(imp.Path.Value, "\"")
					impAlias := path[strings.LastIndex(path, "/")+1:]
					if imp.Name != nil && imp.Name.Name != "_" {
						impAlias = imp.Name.Name
					}
					if impAlias != alias {
						continue
					}
					if de, ok := extern(path, base); ok && de.IsDomain {
						return path, true
					}
				}
			}
			return "", false
		}
		e.TParams, e.Indices = SplitBinders(rawTParams[name], isDomain)
	}
	// Second pass: //goplus:variant markers on struct type decls, paired with
	// the decl to learn the lowered type name and Go field names.
	for _, pf := range parsed {
		filename := pf.name
		for _, decl := range pf.file.Decls {
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
				isIndexed := func(name string) (map[int]bool, int, bool) {
					ie, ok := enums[name]
					if !ok || len(ie.Indices) == 0 {
						return nil, 0, false
					}
					pos := map[int]bool{}
					for _, ib := range ie.Indices {
						pos[ib.Pos] = true
					}
					return pos, len(ie.TParams) + len(ie.Indices), true
				}
				if m.Result != "" {
					full := resultArgsOf(m.Result)
					idxPos := map[int]bool{}
					for _, ib := range e.Indices {
						idxPos[ib.Pos] = true
					}
					var typeArgs, indexArgs []string
					for i, a := range full {
						if idxPos[i] {
							indexArgs = append(indexArgs, a)
							continue
						}
						ea, eerr := EraseIndexArgs(a, isIndexed)
						if eerr != nil {
							return nil, fmt.Errorf("%s: variant %s: %v", filename, m.Name, eerr)
						}
						typeArgs = append(typeArgs, ea)
					}
					v.ResultArgs = typeArgs
					v.IndexArgs = indexArgs
				} else if len(e.Indices) > 0 {
					for _, ib := range e.Indices {
						v.IndexArgs = append(v.IndexArgs, ib.Name)
					}
				}
				existSubst := map[string]string{}
				for _, tp := range parseParamList(m.TParams) {
					v.Exist = append(v.Exist, ExistTP{Name: tp.Name, Bound: tp.Type})
					existSubst[tp.Name] = tp.Type
				}
				params := parseParamList(m.Params)
				fields := flattenFields(st)
				for i, p := range params {
					fieldName := p.Name
					if i < len(fields) {
						fieldName = fields[i]
					}
					erasedType, eerr := EraseIndexArgs(p.Type, isIndexed)
					if eerr != nil {
						return nil, fmt.Errorf("%s: variant %s: %v", filename, m.Name, eerr)
					}
					v.Params = append(v.Params, EnumParam{Name: p.Name, FieldName: fieldName, Type: substWords(erasedType, existSubst), RawType: p.Type})
				}
				e.Variants = append(e.Variants, v)
				break
			}
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

// ExistTP is one bounded existential type parameter of a variant
// (v0.6.0): the hidden name and its interface bound, both in the enum
// package's terms. Fields are stored ERASED to the bound.
type ExistTP struct {
	Name  string
	Bound string
}

// substWords replaces whole-word identifier occurrences in a type text.
func substWords(text string, subst map[string]string) string {
	if len(subst) == 0 {
		return text
	}
	for name, repl := range subst {
		re := regexp.MustCompile(`\b` + regexp.QuoteMeta(name) + `\b`)
		text = re.ReplaceAllString(text, repl)
	}
	return text
}

// EnumsInPkg lists a package's registered enums.
func (r *Registry) EnumsInPkg(pkgPath string) []*Enum {
	var out []*Enum
	for _, e := range r.AllEnums() {
		if e.PkgPath == pkgPath {
			out = append(out, e)
		}
	}
	return out
}
