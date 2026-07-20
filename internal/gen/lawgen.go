package gen

import (
	"fmt"
	"go/format"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"

	"goforge.dev/goplus/internal/diag"
	"goforge.dev/goplus/internal/emit"
	"goforge.dev/goplus/internal/registry"
)

// Law-test generation (v0.5.0). DEFAULT-ON: every instance whose class
// closure declares laws and whose type argument is concrete gets a
// generated <file>_gp_laws_test.go with rapid properties exercising
// every inherited law (through the upcasts). Knobs, via //goplus:laws on
// the instance: `off`; explicit instantiations for generic instances
// (`[int] [string]`); `gen=Name` for a custom rapid generator. A
// package-level `//goplus:laws out=<reldir>` (on the package clause doc)
// emits an EXTERNAL test package instead — the std zero-dependency
// mechanism.

// LawsTestSuffix names generated law-test files.
const LawsTestSuffix = "_gp_laws_test.go"

// planLawTests renders one package's law tests into the outputs map.
func planLawTests(reg *registry.Registry, pkgPath, dir, outRel string, instances []*registry.Instance, skipGens map[string]bool) (map[string][]byte, []diag.Diagnostic) {
	type entry struct {
		inst *registry.Instance
		mode lawsMode
	}
	byFile := map[string][]entry{}
	var files []string
	var diags []diag.Diagnostic

	for _, inst := range instances {
		mode := parseLawsMode(inst.LawsMode)
		if mode.off {
			continue
		}
		ref := inst.Class
		if ref.PkgPath == "" {
			ref.PkgPath = pkgPath
		}
		if len(reg.AllLaws(ref)) == 0 {
			continue
		}
		if inst.Generic && len(mode.instantiations) == 0 {
			continue // generic instances opt in with //goplus:laws [T...]
		}
		if outRel != "" && !inst.Exported() {
			diags = append(diags, diag.Errorf("%s: instance %s is unexported but law tests are routed out of the package (//goplus:laws out=%s); export it or mark it //goplus:laws off",
				inst.SrcPath, inst.Name, outRel))
			continue
		}
		if _, seen := byFile[inst.SrcPath]; !seen {
			files = append(files, inst.SrcPath)
		}
		byFile[inst.SrcPath] = append(byFile[inst.SrcPath], entry{inst: inst, mode: mode})
	}

	out := map[string][]byte{}
	sort.Strings(files)
	for _, srcPath := range files {
		base := strings.TrimSuffix(filepath.Base(srcPath), ".gp")
		var path, pkgName, qual string
		var extraImport string
		declPkgName := byFile[srcPath][0].inst.PkgName
		if outRel == "" {
			path = filepath.Join(dir, base+LawsTestSuffix)
			pkgName = declPkgName
		} else {
			path = filepath.Join(dir, filepath.FromSlash(outRel), base+LawsTestSuffix)
			pkgName = filepath.Base(filepath.FromSlash(outRel))
			qual = declPkgName + "."
			extraImport = "\n\t\"" + pkgPath + "\"\n"
		}

		var b strings.Builder
		b.WriteString(emit.Header(base + ".gp"))
		fmt.Fprintf(&b, "package %s\n\n", pkgName)
		fmt.Fprintf(&b, "import (\n\t\"testing\"\n%s\n\t// goplus:law-imports\n\t\"pgregory.net/rapid\"\n)\n", extraImport)

		neededGens := map[string]bool{}
		for _, e := range byFile[srcPath] {
			text, terr := lawTestFunc(reg, pkgPath, qual, e.inst, e.mode, neededGens)
			if terr != nil {
				diags = append(diags, diag.Errorf("%s: %v", srcPath, terr))
				continue
			}
			b.WriteString("\n" + text)
		}
		for n := range skipGens {
			delete(neededGens, n)
		}
		if len(neededGens) > 0 {
			siblings := GenSiblings(reg.EnumsInPkg(pkgPath))
			names := make([]string, 0, len(neededGens))
			for n := range neededGens {
				names = append(names, n)
			}
			sort.Strings(names)
			for _, n := range names {
				e, ok := reg.LookupEnum(pkgPath, n)
				if !ok {
					continue
				}
				if text, gok := RenderEnumGen(e, siblings, qual); gok {
					b.WriteString("\n" + text)
				}
			}
		}
		rendered := b.String()
		imports := lawTypeImports(srcPath, rendered, pkgPath)
		rendered = strings.Replace(rendered, "\t// goplus:law-imports\n", imports, 1)
		formatted, err := format.Source([]byte(rendered))
		if err != nil {
			diags = append(diags, diag.Errorf("internal error: formatting law tests for %s: %v", srcPath, err))
			continue
		}
		out[path] = formatted
	}
	return out, diags
}

var sourceImportRE = regexp.MustCompile(`(?m)^[ \t]*(?:import[ \t]+)?(?:([A-Za-z_][A-Za-z0-9_]*)[ \t]+)?"([^"]+)"`)
var qualifiedTypeRE = regexp.MustCompile(`\b([A-Za-z_][A-Za-z0-9_]*)\.`)

// lawTypeImports carries imports referenced by law parameter types into the
// generated test. Class laws are stored as source-level type text (for example
// schema.Package), so the test must retain the source file's qualifier mapping.
func lawTypeImports(srcPath, generated, pkgPath string) string {
	src, err := os.ReadFile(srcPath)
	if err != nil {
		return ""
	}
	type imp struct{ alias, path string }
	byAlias := map[string]imp{}
	for _, m := range sourceImportRE.FindAllSubmatch(src, -1) {
		path := string(m[2])
		alias := string(m[1])
		if alias == "" {
			alias = filepath.Base(path)
		}
		if alias != "_" && alias != "." {
			byAlias[alias] = imp{alias: string(m[1]), path: path}
		}
	}
	used := map[string]imp{}
	for _, m := range qualifiedTypeRE.FindAllStringSubmatch(generated, -1) {
		if i, ok := byAlias[m[1]]; ok && i.path != pkgPath && i.path != "pgregory.net/rapid" {
			used[i.path] = i
		}
	}
	paths := make([]string, 0, len(used))
	for path := range used {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	var b strings.Builder
	for _, path := range paths {
		i := used[path]
		if i.alias == "" {
			fmt.Fprintf(&b, "\t%q\n", path)
		} else {
			fmt.Fprintf(&b, "\t%s %q\n", i.alias, path)
		}
	}
	return b.String()
}

type lawsMode struct {
	off            bool
	instantiations []string // bracket groups, e.g. "int", "[]string"
	gen            string   // custom rapid generator name
}

func parseLawsMode(raw string) lawsMode {
	var m lawsMode
	raw = strings.TrimSpace(raw)
	for raw != "" {
		switch {
		case strings.HasPrefix(raw, "off"):
			m.off = true
			raw = strings.TrimSpace(raw[3:])
		case strings.HasPrefix(raw, "gen="):
			rest := raw[4:]
			end := strings.IndexAny(rest, " \t")
			if end < 0 {
				end = len(rest)
			}
			m.gen = rest[:end]
			raw = strings.TrimSpace(rest[end:])
		case strings.HasPrefix(raw, "["):
			depth := 0
			end := -1
			for i, r := range raw {
				if r == '[' {
					depth++
				}
				if r == ']' {
					depth--
					if depth == 0 {
						end = i
						break
					}
				}
			}
			if end < 0 {
				return m
			}
			m.instantiations = append(m.instantiations, strings.TrimSpace(raw[1:end]))
			raw = strings.TrimSpace(raw[end+1:])
		default:
			return m
		}
	}
	return m
}

// lawTestFunc renders one instance's Test<Name>Laws function.
func lawTestFunc(reg *registry.Registry, pkgPath, qual string, inst *registry.Instance, mode lawsMode, neededGens map[string]bool) (string, error) {
	ref := inst.Class
	if ref.PkgPath == "" {
		ref.PkgPath = pkgPath
	}
	laws := reg.AllLaws(ref)

	instantiations := mode.instantiations
	if !inst.Generic {
		instantiations = []string{""}
	}

	var b strings.Builder
	fmt.Fprintf(&b, "func Test%sLaws(t *testing.T) {\n", inst.Name)
	for _, targ := range instantiations {
		suffix := ""
		instRef := qual + inst.Name
		if inst.Generic {
			suffix = "[" + targ + "]"
			instRef += "[" + targ + "]()"
		}
		for _, l := range laws {
			declClass, law := l.Class, l.Law
			decl, ok := reg.LookupClass(declClass)
			if !ok {
				return "", fmt.Errorf("law %s: unknown declaring class %s", law.Name, declClass.Name)
			}
			// Substitute the declaring class's type parameter with the
			// instance's (possibly instantiated) type argument.
			arg := inst.ClassArgs
			if inst.Generic {
				arg = substWord(inst.ClassArgs, firstWord(inst.TParamsText), targ)
			}
			params := registry.ParseParams(substWord(law.Params, decl.TParam, arg))

			recv := instRef
			if declClass != ref {
				recv += ".As" + declClass.Name + "()"
			}
			fmt.Fprintf(&b, "\tt.Run(%q, func(t *testing.T) {\n", declClass.Name+"."+law.Name+suffix)
			b.WriteString("\t\trapid.Check(t, func(rt *rapid.T) {\n")
			var args []string
			for _, p := range params {
				if mode.gen != "" {
					fmt.Fprintf(&b, "\t\t\t%s := %s.Draw(rt, %q)\n", p.Name, qual+mode.gen, p.Name)
				} else if e, isEnum := reg.LookupEnum(pkgPath, p.Type); isEnum && len(e.TParams) == 0 && len(e.Indices) == 0 {
					// Enum-typed law parameter: rapid.Make cannot invent
					// interface values; the derived generator can.
					neededGens[p.Type] = true
					fmt.Fprintf(&b, "\t\t\t%s := Gen%s(rt)\n", p.Name, p.Type)
				} else {
					fmt.Fprintf(&b, "\t\t\t%s := rapid.Make[%s]().Draw(rt, %q)\n", p.Name, p.Type, p.Name)
				}
				args = append(args, p.Name)
			}
			fmt.Fprintf(&b, "\t\t\tif !%s.Law%s(%s) {\n", recv, law.Name, strings.Join(args, ", "))
			var fmtArgs []string
			for _, a := range args {
				fmtArgs = append(fmtArgs, a+"=%v")
			}
			fmt.Fprintf(&b, "\t\t\t\trt.Fatalf(\"law %s violated: %s\", %s)\n",
				law.Name, strings.Join(fmtArgs, " "), strings.Join(args, ", "))
			b.WriteString("\t\t\t}\n\t\t})\n\t})\n")
		}
	}
	b.WriteString("}\n")
	return b.String(), nil
}

// substWord replaces whole-word occurrences of a type parameter name.
func substWord(s, word, repl string) string {
	if word == "" {
		return s
	}
	re := regexp.MustCompile(`\b` + regexp.QuoteMeta(word) + `\b`)
	return re.ReplaceAllString(s, repl)
}

func firstWord(s string) string {
	fields := strings.Fields(s)
	if len(fields) == 0 {
		return ""
	}
	return strings.TrimRight(fields[0], ",")
}

// findLawOrphans lists generated law-test files no longer produced (laws
// switched off, instances removed, or the source .gp gone).
func findLawOrphans(dirs []string, lawsOutByDir map[string]string, outputs map[string][]byte) []string {
	var orphans []string
	seen := map[string]bool{}
	sweep := func(dir string) {
		if seen[dir] {
			return
		}
		seen[dir] = true
		entries, err := os.ReadDir(dir)
		if err != nil {
			return
		}
		for _, e := range entries {
			if e.IsDir() || !strings.HasSuffix(e.Name(), LawsTestSuffix) {
				continue
			}
			path := filepath.Join(dir, e.Name())
			if _, produced := outputs[path]; produced {
				continue
			}
			src, err := os.ReadFile(path)
			if err != nil {
				continue
			}
			if _, generated := emit.GeneratedFrom(src); generated {
				orphans = append(orphans, path)
			}
		}
	}
	for _, dir := range dirs {
		sweep(dir)
		if out := lawsOutByDir[dir]; out != "" {
			sweep(filepath.Join(dir, filepath.FromSlash(out)))
		}
	}
	return orphans
}
