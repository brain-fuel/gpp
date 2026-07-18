// Package resolve rewrites G++ method-syntax uses of generic methods into
// calls (or closures) over the lowered package-level functions.
//
// It runs a fixpoint: type-check the current shadow texts tolerantly with
// go/packages overlays, rewrite every call site whose receiver type is
// known, and repeat — chained calls resolve inside-out, one nesting level
// per iteration. go/types records the receiver's fully-instantiated type
// (and addressability) even when the selector itself fails to resolve,
// which is exactly what each rewrite needs.
package resolve

import (
	"fmt"
	"go/format"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"strings"

	"golang.org/x/tools/go/packages"

	"goforge.dev/gpp/internal/diag"
	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/registry"
)

// maxIterations caps the fixpoint loop; each iteration resolves at least
// one nesting level (pipeline stages resolve left-to-right, a few
// iterations per stage), so real code terminates far earlier.
const maxIterations = 64

// Input configures a fixpoint run.
type Input struct {
	Dir          string                        // working directory for package loading
	Patterns     []string                      // package patterns to load
	Texts        map[string][]byte             // abs output path -> current shadow text
	MethodsByDir map[string][]*registry.Method // dir -> generic methods declared there (PkgPath unset)
	EnumsByDir   map[string][]*registry.Enum   // dir -> enums declared there (PkgPath provisional)
	// v0.5.0 typeclasses (PkgPath provisional, cloned on registration).
	ClassesByDir   map[string][]*registry.Class
	InstancesByDir map[string][]*registry.Instance
}

// Output is the fixpoint result.
type Output struct {
	Texts map[string][]byte
	Diags []diag.Diagnostic
}

// Fixpoint resolves all method-syntax uses across the loaded packages.
func Fixpoint(in *Input) (*Output, error) {
	texts := make(map[string][]byte, len(in.Texts))
	for k, v := range in.Texts {
		texts[k] = v
	}
	reg := registry.New()
	regReady := false
	var diags []diag.Diagnostic

	for iter := 0; ; iter++ {
		if iter == maxIterations {
			diags = append(diags, diag.Errorf("internal error: resolution did not converge after %d iterations", maxIterations))
			break
		}
		cfg := &packages.Config{
			Mode: packages.NeedName | packages.NeedFiles | packages.NeedCompiledGoFiles |
				packages.NeedImports | packages.NeedDeps | packages.NeedTypes |
				packages.NeedSyntax | packages.NeedTypesInfo,
			Dir:     in.Dir,
			Overlay: texts,
		}
		pkgs, err := packages.Load(cfg, in.Patterns...)
		if err != nil {
			return nil, fmt.Errorf("loading packages: %w", err)
		}
		if !regReady {
			if err := buildRegistry(reg, pkgs, in); err != nil {
				return nil, err
			}
			regReady = true
		}
		typesByPath := indexTypesPackages(pkgs)

		runPass := func(report bool) (int, []diag.Diagnostic, error) {
			var passDiags []diag.Diagnostic
			editCount := 0
			for _, pkg := range pkgs {
				for i, fileAST := range pkg.Syntax {
					if i >= len(pkg.CompiledGoFiles) {
						break
					}
					path := pkg.CompiledGoFiles[i]
					src, ours := texts[path]
					if !ours {
						continue
					}
					r := &fileResolver{
						pkg:         pkg,
						typesByPath: typesByPath,
						file:        fileAST,
						src:         src,
						reg:         reg,
						tokFile:     pkg.Fset.File(fileAST.Pos()),
						report:      report,
					}
					edits, fdiags := r.resolve()
					passDiags = append(passDiags, fdiags...)
					if !report && len(edits) > 0 {
						applied, err := lower.Apply(src, edits)
						if err != nil {
							return 0, nil, err
						}
						texts[path] = applied
						editCount += len(edits)
					}
				}
			}
			return editCount, passDiags, nil
		}
		editCount, passDiags, err := runPass(false)
		if err != nil {
			return nil, err
		}
		diags = passDiags
		if editCount == 0 {
			// Converged: one audit pass surfaces precise diagnostics for
			// anything left unresolvable (uninferable constructors,
			// ambiguity requiring qualification).
			_, auditDiags, err := runPass(true)
			if err != nil {
				return nil, err
			}
			diags = auditDiags
			break
		}
	}

	// Format only clean results: diagnostic positions refer to the
	// unformatted texts, and gen remaps them against these bytes.
	if len(diags) == 0 {
		for path, text := range texts {
			if formatted, err := format.Source(text); err == nil {
				texts[path] = formatted
			}
		}
	}
	return &Output{Texts: texts, Diags: diags}, nil
}

// buildRegistry registers local methods and enums under their real package
// paths and discovers dependency methods/enums from marker comments in
// distributed sources.
func buildRegistry(reg *registry.Registry, roots []*packages.Package, in *Input) error {
	var firstErr error
	record := func(err error) {
		if err != nil && firstErr == nil {
			firstErr = err
		}
	}
	packages.Visit(roots, nil, func(pkg *packages.Package) {
		dir := pkgDir(pkg)
		if dir == "" {
			return
		}
		methods, isLocal := in.MethodsByDir[dir]
		if isLocal {
			for _, m := range methods {
				clone := *m
				clone.PkgPath = pkg.PkgPath
				record(reg.Add(&clone))
			}
			for _, e := range in.EnumsByDir[dir] {
				clone := *e
				clone.PkgPath = pkg.PkgPath
				record(reg.AddEnum(&clone))
			}
			for _, c := range in.ClassesByDir[dir] {
				clone := *c
				clone.PkgPath = pkg.PkgPath
				clone.Embeds = append([]registry.ClassRef(nil), c.Embeds...)
				record(reg.AddClass(&clone))
			}
			for _, inst := range in.InstancesByDir[dir] {
				clone := *inst
				clone.PkgPath = pkg.PkgPath
				record(reg.AddInstance(&clone))
			}
			return
		}
		// Dependency package: scan distributed sources for markers.
		for _, file := range pkg.GoFiles {
			src, err := os.ReadFile(file)
			if err != nil {
				continue
			}
			if strings.Contains(string(src), "//gpp:method") {
				methods, err := registry.FromMarkers(pkg.PkgPath, file, src)
				if err == nil { // marker damage in a dep is not fatal
					for _, m := range methods {
						record(reg.Add(m))
					}
				}
			}
			if strings.Contains(string(src), "//gpp:enum") {
				enums, err := registry.EnumsFromMarkers(pkg.PkgPath, file, src)
				if err == nil {
					for _, e := range enums {
						record(reg.AddEnum(e))
					}
				}
			}
			classes, instances, fns, cerr := registry.ClassesFromMarkers(pkg.PkgPath, file, src)
			if cerr == nil { // marker damage in a dep is not fatal
				for _, c := range classes {
					record(reg.AddClass(c))
				}
				for _, inst := range instances {
					record(reg.AddInstance(inst))
				}
				for _, fn := range fns {
					reg.AddConstrainedFn(fn)
				}
			}
		}
	})
	if firstErr == nil {
		registerConstrainedFns(reg, roots, in)
	}
	return firstErr
}

func pkgDir(pkg *packages.Package) string {
	if len(pkg.GoFiles) > 0 {
		return filepath.Dir(pkg.GoFiles[0])
	}
	if len(pkg.CompiledGoFiles) > 0 {
		return filepath.Dir(pkg.CompiledGoFiles[0])
	}
	return ""
}

// indexTypesPackages maps package path -> *types.Package for every package
// reachable from the roots, for lowered-function signature lookups.
func indexTypesPackages(roots []*packages.Package) map[string]*types.Package {
	out := map[string]*types.Package{}
	packages.Visit(roots, nil, func(pkg *packages.Package) {
		if pkg.Types != nil {
			out[pkg.PkgPath] = pkg.Types
		}
	})
	return out
}

// asNamed unwraps aliases and pointers to reach the named receiver type.
// It reports whether one dereference happened.
func asNamed(t types.Type) (named *types.Named, wasPtr bool) {
	t = types.Unalias(t)
	if p, ok := t.(*types.Pointer); ok {
		wasPtr = true
		t = types.Unalias(p.Elem())
	}
	n, _ := t.(*types.Named)
	return n, wasPtr
}

// lookupDirect finds a registry method declared directly on t.
func lookupDirect(reg *registry.Registry, t types.Type, name string) (*registry.Method, *types.Named, bool) {
	named, _ := asNamed(t)
	if named == nil || named.Obj().Pkg() == nil {
		return nil, nil, false
	}
	m, ok := reg.Lookup(named.Obj().Pkg().Path(), named.Obj().Name(), name)
	return m, named, ok
}

func posOf(fset *token.FileSet, pos token.Pos) token.Position { return fset.Position(pos) }
