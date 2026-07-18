// Package registry indexes the generic methods visible to a compilation:
// those declared in the packages being generated, plus those advertised by
// dependency packages via //gpp:method markers in their distributed Go.
package registry

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"sort"
	"strings"

	"goforge.dev/gpp/internal/directive"
	"goforge.dev/gpp/internal/naming"
	"goforge.dev/gpp/internal/syntax"
)

// Method describes one generic method and its lowered function.
type Method struct {
	PkgPath          string
	RecvTypeName     string
	MethodName       string
	FuncName         string
	Pointer          bool
	NumRecvTParams   int
	NumMethodTParams int
}

// Origin renders a human-readable description for diagnostics.
func (m *Method) Origin() string {
	star := ""
	if m.Pointer {
		star = "*"
	}
	return fmt.Sprintf("method (%s%s) %s", star, m.RecvTypeName, m.MethodName)
}

// Registry maps (package path, receiver type name, method name) to methods
// and indexes the enums visible to a compilation.
type Registry struct {
	methods     map[string]*Method
	methodNames map[string]bool
	enumIdx     *enumIndex
}

func New() *Registry {
	return &Registry{methods: map[string]*Method{}, methodNames: map[string]bool{}}
}

func key(pkgPath, recvType, method string) string {
	return pkgPath + "\x00" + recvType + "\x00" + method
}

// Add registers a method. A duplicate (same package, receiver type, and
// method name) is an error — Go itself forbids duplicate method names on a
// type, so this only fires on conflicting marker data or double loading.
func (r *Registry) Add(m *Method) error {
	k := key(m.PkgPath, m.RecvTypeName, m.MethodName)
	if _, exists := r.methods[k]; exists {
		return fmt.Errorf("duplicate generic method %s in package %s", m.Origin(), m.PkgPath)
	}
	r.methods[k] = m
	r.methodNames[m.MethodName] = true
	return nil
}

// Lookup finds the generic method for a receiver's origin type.
func (r *Registry) Lookup(pkgPath, recvTypeName, methodName string) (*Method, bool) {
	m, ok := r.methods[key(pkgPath, recvTypeName, methodName)]
	return m, ok
}

// HasMethodName reports whether any registered generic method has this name
// — a cheap pre-filter for candidate selector expressions.
func (r *Registry) HasMethodName(name string) bool { return r.methodNames[name] }

// All returns every registered method in deterministic order.
func (r *Registry) All() []*Method {
	keys := make([]string, 0, len(r.methods))
	for k := range r.methods {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	out := make([]*Method, 0, len(keys))
	for _, k := range keys {
		out = append(out, r.methods[k])
	}
	return out
}

// MethodsFromFile computes registry entries (with lowered names) for one
// parsed .gpp file, recording each name in tbl. Collisions and invalid
// //gpp:name overrides are returned as errors, one per offending method.
func MethodsFromFile(pkgPath string, f *syntax.File, tbl *naming.Table) ([]*Method, []error) {
	var methods []*Method
	var errs []error
	for _, gm := range f.Methods {
		if gm.NameOverride != "" && !token.IsIdentifier(gm.NameOverride) {
			errs = append(errs, fmt.Errorf("%s: //gpp:name %q is not a valid Go identifier",
				position(f, gm), gm.NameOverride))
			continue
		}
		m := &Method{
			PkgPath:          pkgPath,
			RecvTypeName:     gm.RecvTypeName,
			MethodName:       gm.Decl.Name.Name,
			FuncName:         naming.FuncName(gm.RecvTypeName, gm.Decl.Name.Name, gm.NameOverride),
			Pointer:          gm.RecvPointer,
			NumRecvTParams:   len(gm.RecvTParams),
			NumMethodTParams: countTParams(gm.Decl),
		}
		origin := fmt.Sprintf("%s at %s", m.Origin(), position(f, gm))
		if err := tbl.AddGenerated(m.FuncName, origin); err != nil {
			errs = append(errs, err)
			continue
		}
		methods = append(methods, m)
	}
	return methods, errs
}

func position(f *syntax.File, gm *syntax.GenericMethod) string {
	return f.Fset.Position(gm.Decl.Pos()).String()
}

func countTParams(fd *ast.FuncDecl) int {
	n := 0
	if fd.Type.TypeParams != nil {
		for _, field := range fd.Type.TypeParams.List {
			n += len(field.Names)
		}
	}
	return n
}

// FromMarkers scans a dependency package's Go sources for //gpp:method
// markers and returns the advertised generic methods. Files lacking the
// marker substring should be pre-filtered by the caller for speed; this
// function is still correct without pre-filtering.
func FromMarkers(pkgPath, filename string, src []byte) ([]*Method, error) {
	if !strings.Contains(string(src), "//gpp:method") {
		return nil, nil
	}
	fset := token.NewFileSet()
	astFile, err := parser.ParseFile(fset, filename, src, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		return nil, fmt.Errorf("parsing %s for gpp markers: %w", filename, err)
	}
	var out []*Method
	for _, decl := range astFile.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Doc == nil || fd.Recv != nil {
			continue
		}
		for _, c := range fd.Doc.List {
			mk, ok := directive.ParseMarker(c.Text)
			if !ok {
				continue
			}
			out = append(out, &Method{
				PkgPath:          pkgPath,
				RecvTypeName:     mk.RecvType,
				MethodName:       mk.Method,
				FuncName:         fd.Name.Name,
				Pointer:          mk.Pointer,
				NumRecvTParams:   countNames(mk.RecvTParams),
				NumMethodTParams: countNames(mk.MethodTParams),
			})
			break
		}
	}
	return out, nil
}

func countNames(list string) int {
	if strings.TrimSpace(list) == "" {
		return 0
	}
	return len(strings.Split(list, ","))
}
