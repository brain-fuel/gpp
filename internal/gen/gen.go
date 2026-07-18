// Package gen orchestrates generation: it drives parsing, naming,
// lowering, and emission for every package matched by the CLI's patterns.
package gen

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"

	"goforge.dev/gpp/internal/diag"
	"goforge.dev/gpp/internal/directive"
	"goforge.dev/gpp/internal/emit"
	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/naming"
	"goforge.dev/gpp/internal/registry"
	"goforge.dev/gpp/internal/resolve"
	"goforge.dev/gpp/internal/sourcemap"
	"goforge.dev/gpp/internal/syntax"
)

// Options configures a generation run.
type Options struct {
	Dir      string   // working directory; resolved against pattern paths
	Patterns []string // go-style package patterns; default ["./..."]
	Check    bool     // verify only: report stale outputs, write nothing
	Stage    bool     // after writing, git-add changed/deleted outputs
}

// Result reports what a run did (paths relative to Options.Dir when under it).
type Result struct {
	Written []string // files written (or deleted orphans, in write mode)
	Stale   []string // check mode: outputs missing or out of date
	Orphans []string // generated files whose .gpp source is gone
	Diags   []diag.Diagnostic
}

// Ok reports whether generation completed without diagnostics.
func (r *Result) Ok() bool { return len(r.Diags) == 0 }

// Run executes generation over all matched directories.
func Run(opts Options) (*Result, error) {
	res := &Result{}
	dirs, err := expandPatterns(opts.Dir, opts.Patterns)
	if err != nil {
		return nil, err
	}
	pkgPathRoot, moduleRoot := modulePath(opts.Dir)

	// Pass 1: parse and lower declarations per package.
	outputs := map[string][]byte{}
	methodsByDir := map[string][]*registry.Method{}
	enumsByDir := map[string][]*registry.Enum{}
	gppSources := map[string][]byte{} // output abs path -> .gpp source bytes
	gppPaths := map[string]string{}   // output abs path -> .gpp path (relative)
	var orphans []string
	for _, dir := range dirs {
		idx, diags := loadDir(dir)
		res.Diags = append(res.Diags, diags...)
		if idx != nil && len(diags) == 0 {
			outs, methods, enums, pdiags := processPackage(idx, pkgPath(pkgPathRoot, moduleRoot, dir))
			res.Diags = append(res.Diags, pdiags...)
			for path, content := range outs {
				outputs[path] = content
			}
			methodsByDir[dir] = methods
			enumsByDir[dir] = enums
			for _, f := range idx.files {
				if f.gpp != nil {
					out := emit.OutputPath(f.path)
					gppSources[out] = f.src
					gppPaths[out] = relTo(opts.Dir, f.path)
				}
			}
		}
		orphans = append(orphans, findOrphans(dir)...)
	}
	if len(res.Diags) > 0 {
		res.Diags = diag.Sort(res.Diags)
		return res, nil
	}

	// Pass 2: resolve method-syntax uses against type information —
	// including generic methods advertised by dependencies via markers.
	// This needs a module context; without go.mod, generation stays
	// syntactic.
	if moduleRoot != "" && len(outputs) > 0 {
		in := &resolve.Input{
			Dir:          opts.Dir,
			Patterns:     loadPatterns(opts.Patterns),
			Texts:        outputs,
			MethodsByDir: methodsByDir,
			EnumsByDir:   enumsByDir,
		}
		out, err := resolve.Fixpoint(in)
		if err != nil {
			return nil, err
		}
		if len(out.Diags) > 0 {
			// Resolution diagnostics carry overlay-file positions; remap
			// them onto the .gpp sources they lower from.
			maps := map[string]*sourcemap.Map{}
			for path, text := range out.Texts {
				maps[path] = sourcemap.Build(gppPaths[path], gppSources[path], text)
			}
			for _, d := range out.Diags {
				if m, ok := maps[d.Pos.Filename]; ok {
					if mapped, mok := m.Map(d.Pos); mok {
						d.Pos = mapped
					}
				}
				res.Diags = append(res.Diags, d)
			}
			res.Diags = diag.Sort(res.Diags)
			return res, nil
		}
		outputs = out.Texts

		// Strict backstop: go/types must accept the final result; its
		// errors map back to .gpp positions before anything is written.
		maps := map[string]*sourcemap.Map{}
		for path, text := range outputs {
			maps[path] = sourcemap.Build(gppPaths[path], gppSources[path], text)
		}
		in.Texts = outputs
		bdiags, err := resolve.Backstop(in, maps)
		if err != nil {
			return nil, err
		}
		res.Diags = append(res.Diags, bdiags...)
		if len(res.Diags) > 0 {
			res.Diags = diag.Sort(res.Diags)
			return res, nil
		}
	}

	// Pass 3: write, check, or stage.
	var touched []string
	for _, path := range sortedKeys(outputs) {
		rel := relTo(opts.Dir, path)
		if refusal := emit.CheckOverwrite(path); refusal != nil {
			res.Diags = append(res.Diags, diag.Errorf("%s: %s", rel, refusal.Reason))
			continue
		}
		if opts.Check {
			existing, err := os.ReadFile(path)
			if err != nil || string(existing) != string(outputs[path]) {
				res.Stale = append(res.Stale, rel)
			}
			continue
		}
		wrote, err := emit.WriteIfChanged(path, outputs[path])
		if err != nil {
			return nil, err
		}
		if wrote {
			res.Written = append(res.Written, rel)
			touched = append(touched, path)
		}
	}
	for _, orphan := range orphans {
		rel := relTo(opts.Dir, orphan)
		res.Orphans = append(res.Orphans, rel)
		if opts.Check {
			res.Stale = append(res.Stale, rel)
			continue
		}
		if err := os.Remove(orphan); err != nil {
			return nil, err
		}
		res.Written = append(res.Written, rel)
		touched = append(touched, orphan)
	}

	res.Diags = diag.Sort(res.Diags)
	if opts.Stage && len(touched) > 0 && res.Ok() {
		args := append([]string{"-C", opts.Dir, "add", "--"}, touched...)
		if out, err := exec.Command("git", args...).CombinedOutput(); err != nil {
			return nil, fmt.Errorf("git add: %v\n%s", err, out)
		}
	}
	return res, nil
}

// loadPatterns normalizes CLI patterns for go/packages (relative directory
// patterns need an explicit "./" prefix).
func loadPatterns(patterns []string) []string {
	if len(patterns) == 0 {
		return []string{"./..."}
	}
	out := make([]string, len(patterns))
	for i, p := range patterns {
		p = filepath.ToSlash(p)
		if p != "." && !strings.HasPrefix(p, "./") && !strings.HasPrefix(p, "/") {
			p = "./" + p
		}
		out[i] = p
	}
	return out
}

// loadDir parses a directory's .gpp and authored .go files. Returns nil
// when the directory has no .gpp files.
func loadDir(dir string) (*pkgIndex, []diag.Diagnostic) {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil, []diag.Diagnostic{diag.Errorf("%s: %v", dir, err)}
	}
	var gppNames, goNames []string
	for _, e := range entries {
		if e.IsDir() {
			continue
		}
		switch {
		case strings.HasSuffix(e.Name(), ".gpp"):
			gppNames = append(gppNames, e.Name())
		case strings.HasSuffix(e.Name(), ".go") && !strings.HasSuffix(e.Name(), "_test.go"):
			goNames = append(goNames, e.Name())
		}
	}
	if len(gppNames) == 0 {
		return nil, nil
	}
	sort.Strings(gppNames)
	sort.Strings(goNames)

	idx := &pkgIndex{fset: token.NewFileSet()}
	var diags []diag.Diagnostic
	for _, name := range gppNames {
		path := filepath.Join(dir, name)
		src, err := os.ReadFile(path)
		if err != nil {
			diags = append(diags, diag.Errorf("%s: %v", path, err))
			continue
		}
		f, err := syntax.ParseFile(idx.fset, path, src)
		if err != nil {
			diags = append(diags, parseDiags(err)...)
			continue
		}
		idx.files = append(idx.files, &sourceFile{path: path, base: name, src: src, ast: f.AST, gpp: f})
	}
	for _, name := range goNames {
		path := filepath.Join(dir, name)
		src, err := os.ReadFile(path)
		if err != nil {
			diags = append(diags, diag.Errorf("%s: %v", path, err))
			continue
		}
		if _, generated := emit.GeneratedFrom(src); generated {
			continue
		}
		astFile, err := parser.ParseFile(idx.fset, path, src, parser.ParseComments|parser.SkipObjectResolution)
		if err != nil {
			diags = append(diags, parseDiags(err)...)
			continue
		}
		idx.files = append(idx.files, &sourceFile{path: path, base: name, src: src, ast: astFile})
	}
	return idx, diags
}

// processPackage lowers every .gpp file of one package to output bytes,
// also returning the package's generic methods and enums for the
// resolution registry.
func processPackage(idx *pkgIndex, pkgPath string) (map[string][]byte, []*registry.Method, []*registry.Enum, []diag.Diagnostic) {
	var diags []diag.Diagnostic

	tbl := naming.NewTable()
	for _, f := range idx.files {
		for _, d := range naming.TopLevelDecls(idx.fset, f.ast) {
			tbl.AddAuthored(d.Name, d.Position)
		}
	}
	enums, ediags := planEnums(idx, pkgPath, tbl)
	diags = append(diags, ediags...)
	enumNames := map[string]bool{}
	for _, m := range enums.models {
		enumNames[m.Name] = true
	}

	methodNames := map[*syntax.GenericMethod]string{}
	enumMethods := map[*sourceFile][]*syntax.GenericMethod{}
	var allMethods []*registry.Method
	for _, f := range idx.files {
		if f.gpp == nil {
			continue
		}
		// TODO(v0.4.0): removed as kleisli lowering lands (phase 7).
		for _, c := range f.gpp.Composes {
			for _, k := range c.Ops {
				if k == syntax.ComposeKleisli {
					diags = append(diags, diag.At(idx.fset.Position(c.Bad.From),
						"kleisli composition lowering is not implemented yet"))
					break
				}
			}
		}
		// Enum receivers must be values: the lowered receiver type is the
		// sealed interface.
		for _, gm := range f.gpp.Methods {
			if enumNames[gm.RecvTypeName] && gm.RecvPointer {
				diags = append(diags, diag.At(idx.fset.Position(gm.Decl.Recv.Pos()),
					"enum receiver must not be a pointer; %s is an interface after lowering", gm.RecvTypeName))
			}
		}
		methods, errs := registry.MethodsFromFile(pkgPath, f.gpp, tbl)
		for _, err := range errs {
			diags = append(diags, diag.Errorf("%s", err))
		}
		allMethods = append(allMethods, methods...)
		// MethodsFromFile returns methods in file order, skipping errored
		// ones; align by (type, method) name.
		for _, m := range methods {
			for _, gm := range f.gpp.Methods {
				if gm.RecvTypeName == m.RecvTypeName && gm.Decl.Name.Name == m.MethodName {
					methodNames[gm] = m.FuncName
				}
			}
		}
		// Plain (non-generic) methods on enum receivers also lower to
		// package functions — interfaces cannot carry method bodies.
		for _, decl := range f.gpp.AST.Decls {
			fd, ok := decl.(*ast.FuncDecl)
			if !ok || fd.Recv == nil || fd.Type.TypeParams != nil {
				continue
			}
			gm, err := syntax.NewMethod(fd)
			if err != nil || !enumNames[gm.RecvTypeName] {
				continue
			}
			if gm.RecvPointer {
				diags = append(diags, diag.At(idx.fset.Position(fd.Recv.Pos()),
					"enum receiver must not be a pointer; %s is an interface after lowering", gm.RecvTypeName))
				continue
			}
			if gm.NameOverride != "" && !token.IsIdentifier(gm.NameOverride) {
				diags = append(diags, diag.At(idx.fset.Position(fd.Pos()),
					"//gpp:name %q is not a valid Go identifier", gm.NameOverride))
				continue
			}
			m := &registry.Method{
				PkgPath:        pkgPath,
				RecvTypeName:   gm.RecvTypeName,
				MethodName:     fd.Name.Name,
				FuncName:       naming.FuncName(gm.RecvTypeName, fd.Name.Name, gm.NameOverride),
				NumRecvTParams: len(gm.RecvTParams),
			}
			origin := fmt.Sprintf("%s at %s", m.Origin(), idx.fset.Position(fd.Pos()))
			if err := tbl.AddGenerated(m.FuncName, origin); err != nil {
				diags = append(diags, diag.Errorf("%s", err))
				continue
			}
			allMethods = append(allMethods, m)
			methodNames[gm] = m.FuncName
			enumMethods[f] = append(enumMethods[f], gm)
		}
	}
	if len(diags) > 0 {
		return nil, nil, nil, diags
	}

	outputs := map[string][]byte{}
	for _, f := range idx.files {
		if f.gpp == nil {
			continue
		}
		var edits []lower.Edit
		for _, e := range f.gpp.Enums {
			if spec, ok := enums.specs[e]; ok {
				edits = append(edits, lower.EnumEdits(f.gpp, e, spec)...)
			}
		}
		hedits, hdiags := lower.NewHoister(f.gpp, len(f.gpp.Matches)).FileEdits()
		diags = append(diags, hdiags...)
		edits = append(edits, hedits...)
		for _, gm := range append(append([]*syntax.GenericMethod{}, f.gpp.Methods...), enumMethods[f]...) {
			funcName := methodNames[gm]
			tparams, err := receiverTParams(idx, gm)
			if err != nil {
				diags = append(diags, diag.At(idx.fset.Position(gm.Decl.Pos()), "%v", err))
				continue
			}
			edits = append(edits, lower.Decl(f.gpp, gm, funcName, tparams)...)
			edits = append(edits, lower.MarkerInsert(f.gpp, gm, markerFor(gm, funcName)))
		}
		if len(diags) > 0 {
			continue
		}
		body, err := lower.Apply(f.src, edits)
		if err != nil {
			diags = append(diags, diag.Errorf("%s: %v", f.path, err))
			continue
		}
		out, err := emit.Finish(f.base, body)
		if err != nil {
			diags = append(diags, diag.Errorf("%s: %v", f.path, err))
			continue
		}
		outputs[emit.OutputPath(f.path)] = out
	}
	if len(diags) > 0 {
		return nil, nil, nil, diags
	}
	return outputs, allMethods, enums.models, nil
}

// markerFor renders the //gpp:method marker comment for a lowered method.
func markerFor(gm *syntax.GenericMethod, funcName string) string {
	var tparams []string
	if gm.Decl.Type.TypeParams != nil {
		for _, field := range gm.Decl.Type.TypeParams.List {
			for _, n := range field.Names {
				tparams = append(tparams, n.Name)
			}
		}
	}
	return directive.Marker{
		Pointer:       gm.RecvPointer,
		RecvType:      gm.RecvTypeName,
		RecvTParams:   strings.Join(gm.RecvTParams, ", "),
		Method:        gm.Decl.Name.Name,
		MethodTParams: strings.Join(tparams, ", "),
		FuncName:      funcName,
	}.String()
}

// findOrphans lists generated files in dir whose .gpp source no longer
// exists.
func findOrphans(dir string) []string {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil
	}
	var orphans []string
	for _, e := range entries {
		name := e.Name()
		if e.IsDir() || !strings.HasSuffix(name, emit.GeneratedSuffix) {
			continue
		}
		path := filepath.Join(dir, name)
		src, err := os.ReadFile(path)
		if err != nil {
			continue
		}
		if _, generated := emit.GeneratedFrom(src); !generated {
			continue
		}
		gppName := strings.TrimSuffix(name, emit.GeneratedSuffix) + ".gpp"
		if _, err := os.Stat(filepath.Join(dir, gppName)); os.IsNotExist(err) {
			orphans = append(orphans, path)
		}
	}
	sort.Strings(orphans)
	return orphans
}

func parseDiags(err error) []diag.Diagnostic {
	if list, ok := err.(scanner.ErrorList); ok {
		out := make([]diag.Diagnostic, len(list))
		for i, e := range list {
			out[i] = diag.At(e.Pos, "%s", e.Msg)
		}
		return out
	}
	return []diag.Diagnostic{diag.Errorf("%v", err)}
}

func pkgPath(root, moduleRoot, dir string) string {
	if root == "" || moduleRoot == "" {
		return filepath.Base(dir)
	}
	rel, err := filepath.Rel(moduleRoot, dir)
	if err != nil || rel == "." {
		return root
	}
	return root + "/" + filepath.ToSlash(rel)
}

func relTo(base, path string) string {
	rel, err := filepath.Rel(base, path)
	if err != nil || strings.HasPrefix(rel, "..") {
		return path
	}
	return rel
}

func sortedKeys(m map[string][]byte) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}
