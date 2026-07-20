package registry

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"strings"

	"goforge.dev/goplus/internal/core"
)

// Total functions (v0.7.0). A `//goplus:total Name(params…) nat` marker
// sits above the erased func in the generated file; the erased Go body
// IS the definition (pure nat code on ints), so reconstruction
// re-elaborates it — no body duplication in comments. Defs are keyed
// canonically "pkgpath.Name" everywhere (Call.Fn, Defs maps, lookups).

// TotalPrefix is the marker directive.
const TotalPrefix = "//goplus:total"

// Total is one total function.
type Total struct {
	PkgPath string
	Name    string
	Sig     string // original signature text, e.g. "Plus(a, b nat) nat"
	Def     *core.Def
}

// Key returns the canonical definition key.
func (t *Total) Key() string { return t.PkgPath + "." + t.Name }

// Exported reports whether the total is visible to importers.
func (t *Total) Exported() bool { return ast.IsExported(t.Name) }

type totalIndex struct {
	byKey map[string]*Total
}

func (r *Registry) totals() *totalIndex {
	if r.totalIdx == nil {
		r.totalIdx = &totalIndex{byKey: map[string]*Total{}}
	}
	return r.totalIdx
}

// AddTotal registers one total function.
func (r *Registry) AddTotal(t *Total) error {
	idx := r.totals()
	if prev, ok := idx.byKey[t.Key()]; ok && prev.Sig != t.Sig {
		return fmt.Errorf("conflicting total markers for %s", t.Key())
	}
	idx.byKey[t.Key()] = t
	return nil
}

// LookupTotal finds a total function by package path and name.
func (r *Registry) LookupTotal(pkgPath, name string) (*Total, bool) {
	t, ok := r.totals().byKey[pkgPath+"."+name]
	return t, ok
}

// TotalDefs returns every registered definition keyed canonically —
// the evaluator's Defs environment.
func (r *Registry) TotalDefs() core.Defs {
	out := core.Defs{}
	for k, t := range r.totals().byKey {
		if t.Def != nil {
			out[k] = t.Def
		}
	}
	return out
}

// TotalsInPkg lists a package's totals.
func (r *Registry) TotalsInPkg(pkgPath string) []*Total {
	var out []*Total
	for _, t := range r.totals().byKey {
		if t.PkgPath == pkgPath {
			out = append(out, t)
		}
	}
	return out
}

// TotalsFromMarkers reconstructs totals from one generated file.
func TotalsFromMarkers(pkgPath, filename string, src []byte) ([]*Total, error) {
	if !strings.Contains(string(src), TotalPrefix) {
		return nil, nil
	}
	fset := token.NewFileSet()
	astFile, err := parser.ParseFile(fset, filename, src, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		return nil, fmt.Errorf("parsing %s for goplus markers: %w", filename, err)
	}
	resolve := markerCallResolver(pkgPath, astFile)
	var out []*Total
	for _, decl := range astFile.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Doc == nil || fd.Recv != nil {
			continue
		}
		for _, c := range fd.Doc.List {
			rest, ok := strings.CutPrefix(c.Text, TotalPrefix+" ")
			if !ok {
				continue
			}
			sig := strings.TrimSpace(rest)
			if !strings.HasPrefix(sig, fd.Name.Name+"(") {
				return nil, fmt.Errorf("%s: marker %q does not match func %s", filename, sig, fd.Name.Name)
			}
			params := paramNames(fd)
			def, err := core.ElabFuncBody(pkgPath+"."+fd.Name.Name, params, fd.Body, resolve)
			if err != nil {
				return nil, fmt.Errorf("%s: reconstructing total %s: %w", filename, fd.Name.Name, err)
			}
			out = append(out, &Total{PkgPath: pkgPath, Name: fd.Name.Name, Sig: sig, Def: def})
		}
	}
	return out, nil
}

// paramNames flattens a func's parameter names in order.
func paramNames(fd *ast.FuncDecl) []string {
	var out []string
	if fd.Type.Params == nil {
		return out
	}
	for _, f := range fd.Type.Params.List {
		for _, n := range f.Names {
			out = append(out, n.Name)
		}
	}
	return out
}

// markerCallResolver canonicalizes callees inside one file: bare idents
// are this package's totals; selector calls resolve through the file's
// imports.
func markerCallResolver(pkgPath string, file *ast.File) core.CallResolver {
	imports := map[string]string{}
	for _, imp := range file.Imports {
		path := strings.Trim(imp.Path.Value, `"`)
		name := path[strings.LastIndex(path, "/")+1:]
		if imp.Name != nil {
			name = imp.Name.Name
		}
		imports[name] = path
	}
	return func(fun ast.Expr) (string, bool) {
		switch f := fun.(type) {
		case *ast.Ident:
			return pkgPath + "." + f.Name, true
		case *ast.SelectorExpr:
			alias, ok := f.X.(*ast.Ident)
			if !ok {
				return "", false
			}
			if path, found := imports[alias.Name]; found {
				return path + "." + f.Sel.Name, true
			}
		}
		return "", false
	}
}
