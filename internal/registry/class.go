package registry

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"strconv"
	"strings"

	"goforge.dev/gpp/internal/directive"
)

// Typeclass registry (v0.5.0): classes, named instances, and
// dictionary-taking (constrained) functions, reconstructed locally from
// side tables and cross-package from //gpp:class / //gpp:law /
// //gpp:default / //gpp:instance / //gpp:fn markers.

// ClassRef names a class. An empty PkgPath means "same package as the
// referrer" and is resolved when the declaration is registered.
type ClassRef struct {
	PkgPath string
	Name    string
}

func (r ClassRef) String() string {
	if r.PkgPath == "" {
		return r.Name
	}
	return strconv.Quote(r.PkgPath) + "." + r.Name
}

// ClassLaw is one declared law: name plus verbatim parameter text.
type ClassLaw struct {
	Name   string
	Params string
}

// Class is one class declaration. For local classes Ops holds the LOCAL
// operations only (ancestors contribute through the embed graph); for
// dependency classes reconstructed from a flattened witness struct, Ops
// holds the full closure — AllOps unions either way.
type Class struct {
	PkgPath  string
	Name     string
	TParam   string // the single type parameter's name
	Embeds   []ClassRef
	Ops      []string
	Laws     []ClassLaw
	Defaults []string // op names carrying default implementations
}

// Instance is one named instance declaration.
type Instance struct {
	PkgPath     string
	Name        string
	Class       ClassRef
	ClassArgs   string // the single type-argument text, e.g. "int" or "[]T"
	Generic     bool   // lowered to a function
	TParamsText string // e.g. "T any" for generic instances
	LawsMode    string // raw //gpp:laws directive value; "" = default
}

// Exported reports whether the instance value is exported.
func (i *Instance) Exported() bool {
	return len(i.Name) > 0 && i.Name[0] >= 'A' && i.Name[0] <= 'Z'
}

// DictParam is one dictionary parameter of a constrained function.
type DictParam struct {
	TParam    string
	Class     ClassRef
	ParamName string
}

// ConstrainedFn is a function whose type parameters carry class
// constraints, lowered to leading dictionary value parameters.
type ConstrainedFn struct {
	PkgPath string
	Name    string
	Dicts   []DictParam
}

type classIndex struct {
	classes    map[string]*Class         // pkgPath\x00name
	instances  map[string][]*Instance    // pkgPath -> instances (decl order)
	instByName map[string]*Instance      // pkgPath\x00name
	fns        map[string]*ConstrainedFn // pkgPath\x00name
	fnNames    map[string]bool           // fast pre-filter on call sites
	classNames map[string]bool           // fast pre-filter on constraints
}

func (r *Registry) classIdx() *classIndex {
	if r.classIdxV == nil {
		r.classIdxV = &classIndex{
			classes:    map[string]*Class{},
			instances:  map[string][]*Instance{},
			instByName: map[string]*Instance{},
			fns:        map[string]*ConstrainedFn{},
			fnNames:    map[string]bool{},
			classNames: map[string]bool{},
		}
	}
	return r.classIdxV
}

// AddClass registers a class, resolving same-package embed refs.
func (r *Registry) AddClass(c *Class) error {
	idx := r.classIdx()
	key := c.PkgPath + "\x00" + c.Name
	if _, dup := idx.classes[key]; dup {
		return fmt.Errorf("class %s declared twice in %s", c.Name, c.PkgPath)
	}
	for i := range c.Embeds {
		if c.Embeds[i].PkgPath == "" {
			c.Embeds[i].PkgPath = c.PkgPath
		}
	}
	idx.classes[key] = c
	idx.classNames[c.Name] = true
	return nil
}

// AddInstance registers an instance.
func (r *Registry) AddInstance(i *Instance) error {
	idx := r.classIdx()
	key := i.PkgPath + "\x00" + i.Name
	if _, dup := idx.instByName[key]; dup {
		return fmt.Errorf("instance %s declared twice in %s", i.Name, i.PkgPath)
	}
	if i.Class.PkgPath == "" {
		i.Class.PkgPath = i.PkgPath
	}
	idx.instByName[key] = i
	idx.instances[i.PkgPath] = append(idx.instances[i.PkgPath], i)
	return nil
}

// AddConstrainedFn registers a dictionary-taking function.
func (r *Registry) AddConstrainedFn(fn *ConstrainedFn) {
	idx := r.classIdx()
	idx.fns[fn.PkgPath+"\x00"+fn.Name] = fn
	idx.fnNames[fn.Name] = true
}

// LookupClass finds a class by package path and name.
func (r *Registry) LookupClass(ref ClassRef) (*Class, bool) {
	c, ok := r.classIdx().classes[ref.PkgPath+"\x00"+ref.Name]
	return c, ok
}

// HasClassName reports whether any registered class has this name.
func (r *Registry) HasClassName(name string) bool { return r.classIdx().classNames[name] }

// HasConstrainedFnName is the call-site pre-filter.
func (r *Registry) HasConstrainedFnName(name string) bool { return r.classIdx().fnNames[name] }

// LookupConstrainedFn finds a constrained function.
func (r *Registry) LookupConstrainedFn(pkgPath, name string) (*ConstrainedFn, bool) {
	fn, ok := r.classIdx().fns[pkgPath+"\x00"+name]
	return fn, ok
}

// LookupInstance finds an instance by package path and name.
func (r *Registry) LookupInstance(pkgPath, name string) (*Instance, bool) {
	i, ok := r.classIdx().instByName[pkgPath+"\x00"+name]
	return i, ok
}

// InstancesInPkg lists a package's instances in declaration order.
func (r *Registry) InstancesInPkg(pkgPath string) []*Instance {
	return r.classIdx().instances[pkgPath]
}

// Ancestors returns the deduped transitive embed closure of a class
// (diamonds collapse), excluding the class itself, in BFS order.
func (r *Registry) Ancestors(ref ClassRef) []ClassRef {
	var out []ClassRef
	seen := map[ClassRef]bool{ref: true}
	queue := []ClassRef{ref}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		c, ok := r.LookupClass(cur)
		if !ok {
			continue
		}
		for _, e := range c.Embeds {
			if seen[e] {
				continue
			}
			seen[e] = true
			out = append(out, e)
			queue = append(queue, e)
		}
	}
	return out
}

// SubsumesRef reports whether an instance of class `have` satisfies a
// constraint on class `want` (identity or ancestor).
func (r *Registry) SubsumesRef(have, want ClassRef) bool {
	if have == want {
		return true
	}
	for _, a := range r.Ancestors(have) {
		if a == want {
			return true
		}
	}
	return false
}

// AllOps returns the union of a class's own and ancestral operation
// names.
func (r *Registry) AllOps(ref ClassRef) map[string]ClassRef {
	out := map[string]ClassRef{}
	add := func(cr ClassRef) {
		if c, ok := r.LookupClass(cr); ok {
			for _, op := range c.Ops {
				if _, have := out[op]; !have {
					out[op] = cr
				}
			}
		}
	}
	add(ref)
	for _, a := range r.Ancestors(ref) {
		add(a)
	}
	return out
}

// AllLaws returns a class's own and inherited laws with the class that
// declares each (closure BFS order, declaration order within a class).
func (r *Registry) AllLaws(ref ClassRef) []struct {
	Class ClassRef
	Law   ClassLaw
} {
	var out []struct {
		Class ClassRef
		Law   ClassLaw
	}
	add := func(cr ClassRef) {
		if c, ok := r.LookupClass(cr); ok {
			for _, l := range c.Laws {
				out = append(out, struct {
					Class ClassRef
					Law   ClassLaw
				}{cr, l})
			}
		}
	}
	add(ref)
	for _, a := range r.Ancestors(ref) {
		add(a)
	}
	return out
}

// AllDefaults returns op name -> declaring class for every default in the
// closure.
func (r *Registry) AllDefaults(ref ClassRef) map[string]ClassRef {
	out := map[string]ClassRef{}
	add := func(cr ClassRef) {
		if c, ok := r.LookupClass(cr); ok {
			for _, op := range c.Defaults {
				if _, have := out[op]; !have {
					out[op] = cr
				}
			}
		}
	}
	add(ref)
	for _, a := range r.Ancestors(ref) {
		add(a)
	}
	return out
}

// ParseClassRefText parses a marker-form class reference with optional
// type args: `Monoid[int]`, `"pkg/path".Monoid[[]T]`, or bare
// `Monoid`. localPkg fills unqualified references.
func ParseClassRefText(text, localPkg string) (ref ClassRef, args string, ok bool) {
	text = strings.TrimSpace(text)
	if strings.HasPrefix(text, `"`) {
		end := strings.Index(text[1:], `"`)
		if end < 0 {
			return ClassRef{}, "", false
		}
		ref.PkgPath = text[1 : 1+end]
		rest := text[2+end:]
		if !strings.HasPrefix(rest, ".") {
			return ClassRef{}, "", false
		}
		text = rest[1:]
	} else {
		ref.PkgPath = localPkg
	}
	if i := strings.Index(text, "["); i >= 0 {
		ref.Name = strings.TrimSpace(text[:i])
		if !strings.HasSuffix(text, "]") {
			return ClassRef{}, "", false
		}
		args = strings.TrimSpace(text[i+1 : len(text)-1])
	} else {
		ref.Name = strings.TrimSpace(text)
	}
	return ref, args, ref.Name != ""
}

// ClassesFromMarkers reconstructs classes, instances, and constrained
// functions from a dependency's distributed Go source. Tolerant: damaged
// markers hide a declaration, never fatal.
func ClassesFromMarkers(pkgPath, filename string, src []byte) (classes []*Class, instances []*Instance, fns []*ConstrainedFn, err error) {
	text := string(src)
	if !strings.Contains(text, "//gpp:class") && !strings.Contains(text, "//gpp:instance") && !strings.Contains(text, "//gpp:fn") {
		return nil, nil, nil, nil
	}
	fset := token.NewFileSet()
	astFile, perr := parser.ParseFile(fset, filename, src, parser.ParseComments|parser.SkipObjectResolution)
	if perr != nil {
		return nil, nil, nil, fmt.Errorf("parsing %s for gpp markers: %w", filename, perr)
	}
	byName := map[string]*Class{}

	// Classes: markers on struct type decls; ops from the (flattened)
	// witness struct's named func fields.
	for _, decl := range astFile.Decls {
		gd, ok := decl.(*ast.GenDecl)
		if !ok || gd.Tok != token.TYPE || len(gd.Specs) != 1 {
			continue
		}
		ts, tok := gd.Specs[0].(*ast.TypeSpec)
		if !tok {
			continue
		}
		st, sok := ts.Type.(*ast.StructType)
		if !sok {
			continue
		}
		for _, line := range docLines(gd.Doc) {
			m, mok := directive.ParseClassMarker(line)
			if !mok || m.Name != ts.Name.Name {
				continue
			}
			c := &Class{PkgPath: pkgPath, Name: m.Name, TParam: firstIdent(m.TParams)}
			for _, e := range m.Embeds {
				if ref, _, rok := ParseClassRefText(e, pkgPath); rok {
					c.Embeds = append(c.Embeds, ref)
				}
			}
			for _, f := range st.Fields.List {
				for _, n := range f.Names {
					c.Ops = append(c.Ops, n.Name)
				}
			}
			byName[c.Name] = c
			classes = append(classes, c)
			break
		}
	}
	// Laws and defaults: markers on witness methods.
	for _, decl := range astFile.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Recv == nil {
			continue
		}
		for _, line := range docLines(fd.Doc) {
			if m, mok := directive.ParseLawMarker(line); mok {
				if c := byName[m.ClassName]; c != nil {
					c.Laws = append(c.Laws, ClassLaw{Name: m.Name, Params: m.Params})
				}
				break
			}
			if m, mok := directive.ParseDefaultMarker(line); mok {
				if c := byName[m.ClassName]; c != nil {
					c.Defaults = append(c.Defaults, m.Name)
				}
				break
			}
		}
	}
	// Instances and constrained fns: markers on values and functions.
	for _, decl := range astFile.Decls {
		var doc *ast.CommentGroup
		generic := false
		switch d := decl.(type) {
		case *ast.GenDecl:
			doc = d.Doc
		case *ast.FuncDecl:
			doc = d.Doc
			generic = d.Recv == nil && d.Type.TypeParams != nil
		default:
			continue
		}
		for _, line := range docLines(doc) {
			if m, mok := directive.ParseInstanceMarker(line); mok {
				ref, args, rok := ParseClassRefText(m.Class, pkgPath)
				if !rok {
					break
				}
				instances = append(instances, &Instance{
					PkgPath: pkgPath, Name: m.Name,
					Class: ref, ClassArgs: args,
					Generic: m.TParams != "" || generic, TParamsText: m.TParams,
				})
				break
			}
			if m, mok := directive.ParseFnMarker(line); mok {
				fn := &ConstrainedFn{PkgPath: pkgPath, Name: m.Name}
				for _, pair := range splitTopLevel(m.Constraints, ',') {
					fields := strings.Fields(strings.TrimSpace(pair))
					if len(fields) < 2 {
						continue
					}
					ref, _, rok := ParseClassRefText(strings.Join(fields[1:], " "), pkgPath)
					if !rok {
						continue
					}
					fn.Dicts = append(fn.Dicts, DictParam{TParam: fields[0], Class: ref})
				}
				if len(fn.Dicts) > 0 {
					fns = append(fns, fn)
				}
				break
			}
		}
	}
	return classes, instances, fns, nil
}

func firstIdent(s string) string {
	fields := strings.Fields(s)
	if len(fields) == 0 {
		return ""
	}
	return strings.TrimRight(fields[0], ",")
}
