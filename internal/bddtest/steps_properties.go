package bddtest

import (
	"fmt"
	"go/token"
	"math/rand"
	"os"
	"path/filepath"
	"strings"

	"github.com/cucumber/godog"
	"pgregory.net/rapid"

	"goforge.dev/goplus/internal/emit"
	"goforge.dev/goplus/internal/gen"
	"goforge.dev/goplus/internal/syntax"
)

func initPropertySteps(sc *godog.ScenarioContext, w func() *World) {
	sc.Step(`^for any plain Go file, parsing as Go\+ succeeds with no generic methods$`, func() error {
		return w().checkProperty(func(rt *rapid.T) {
			src := plainGoSource(rt)
			f, err := syntax.ParseFile(token.NewFileSet(), "prop.gp", []byte(src))
			if err != nil {
				rt.Fatalf("valid Go rejected by the Go+ frontend: %v\n%s", err, src)
			}
			if len(f.Methods) != 0 {
				rt.Fatalf("plain Go produced %d generic methods\n%s", len(f.Methods), src)
			}
		})
	})

	sc.Step(`^for any plain Go file, the emitted output is the header plus the source unchanged$`, func() error {
		world := w()
		return world.checkProperty(func(rt *rapid.T) {
			src := plainGoSource(rt)
			dir := world.freshPropDir(rt)
			mustWrite(rt, filepath.Join(dir, "in.gp"), src)
			res := mustGen(rt, dir)
			_ = res
			got := mustRead(rt, filepath.Join(dir, "in_gp.go"))
			want := emit.Header("in.gp") + src
			if got != want {
				rt.Fatalf("passthrough not lossless:\n--- got ---\n%s\n--- want ---\n%s", got, want)
			}
		})
	})

	sc.Step(`^for any Go\+ package, generating twice produces identical bytes and no rewrites$`, func() error {
		world := w()
		return world.checkProperty(func(rt *rapid.T) {
			p := goplusPackageGen(rt)
			dir := world.freshPropDir(rt)
			mustWrite(rt, filepath.Join(dir, "in.gp"), p.Source(nil))
			mustGen(rt, dir)
			first := mustRead(rt, filepath.Join(dir, "in_gp.go"))
			res := mustGen(rt, dir)
			if len(res.Written) != 0 {
				rt.Fatalf("second gen rewrote files: %v", res.Written)
			}
			second := mustRead(rt, filepath.Join(dir, "in_gp.go"))
			if first != second {
				rt.Fatalf("output changed between identical runs")
			}
		})
	})

	sc.Step(`^for any Go\+ package, permuting declarations preserves the lowered function names$`, func() error {
		world := w()
		return world.checkProperty(func(rt *rapid.T) {
			p := goplusPackageGen(rt)
			order := permutation(rt, len(p.Decls))

			dirA := world.freshPropDir(rt)
			dirB := world.freshPropDir(rt)
			mustWrite(rt, filepath.Join(dirA, "in.gp"), p.Source(nil))
			mustWrite(rt, filepath.Join(dirB, "in.gp"), p.Source(order))
			mustGen(rt, dirA)
			mustGen(rt, dirB)
			outA := mustRead(rt, filepath.Join(dirA, "in_gp.go"))
			outB := mustRead(rt, filepath.Join(dirB, "in_gp.go"))
			for _, name := range p.MethodNames {
				needle := "func " + name + "["
				if !strings.Contains(outA, needle) {
					rt.Fatalf("expected lowered name %s missing from original order:\n%s", name, outA)
				}
				if !strings.Contains(outB, needle) {
					rt.Fatalf("expected lowered name %s missing from permuted order:\n%s", name, outB)
				}
			}
			for _, name := range p.VariantNames {
				needle := "type " + name
				if !strings.Contains(outA, needle) || !strings.Contains(outB, needle) {
					rt.Fatalf("expected variant struct %s missing under permutation", name)
				}
			}
		})
	})

	sc.Step(`^for sampled pipelines, the pipeline equals its hand-written lowering and no carriers survive$`, func() error {
		world := w()
		rng := rand.New(rand.NewSource(20260719))
		pool := []struct{ name, body string }{
			{"inc", "return n + 1"},
			{"double", "return n * 2"},
			{"negate", "return -n"},
			{"square", "return n * n"},
		}
		for sample := 0; sample < 4; sample++ {
			k := 1 + rng.Intn(4)
			head := rng.Intn(20)
			var stages []string
			for i := 0; i < k; i++ {
				stages = append(stages, pool[rng.Intn(len(pool))].name)
			}
			// Hand-written nested lowering, inside-out.
			nested := fmt.Sprintf("%d", head)
			pipeline := fmt.Sprintf("%d", head)
			for _, s := range stages {
				nested = s + "(" + nested + ")"
				pipeline += " |> " + s
			}
			var b strings.Builder
			b.WriteString("package main\n\nimport \"fmt\"\n\n")
			for _, p := range pool {
				fmt.Fprintf(&b, "func %s(n int) int { %s }\n\n", p.name, p.body)
			}
			fmt.Fprintf(&b, "func main() {\n\tfmt.Println((%s) == %s)\n}\n", pipeline, nested)

			dir := filepath.Join(world.Dir, fmt.Sprintf("flow%d", sample))
			if err := os.MkdirAll(dir, 0o755); err != nil {
				return err
			}
			if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte("module example.com/flow\n\ngo 1.24\n"), 0o644); err != nil {
				return err
			}
			if err := os.WriteFile(filepath.Join(dir, "main.gp"), []byte(b.String()), 0o644); err != nil {
				return err
			}
			res, err := gen.Run(gen.Options{Dir: dir, Patterns: []string{"."}})
			if err != nil {
				return fmt.Errorf("sample %d: %v", sample, err)
			}
			if !res.Ok() {
				return fmt.Errorf("sample %d (%s): diagnostics: %v", sample, pipeline, res.Diags)
			}
			out, rerr := os.ReadFile(filepath.Join(dir, "main_gp.go"))
			if rerr != nil {
				return rerr
			}
			for _, leftover := range []string{
				"__gp_bare_", "__gp_comp(", "//goplus:pattern", "case nil:",
				"__gp_seg", "__gp_dot(", "__gp_kcomp_", "__gp_try", "__gp_val",
				"//goplus:refine",
			} {
				if strings.Contains(string(out), leftover) {
					return fmt.Errorf("sample %d: emitted file contains %q", sample, leftover)
				}
			}
			// The lowering must be exactly the hand-written nesting.
			if !strings.Contains(string(out), "("+nested+") == "+nested) {
				return fmt.Errorf("sample %d: pipeline did not lower to %s:\n%s", sample, nested, out)
			}
		}
		return nil
	})

	sc.Step(`^for sampled enums, generation succeeds exactly when the match covers every variant$`, func() error {
		world := w()
		rng := rand.New(rand.NewSource(20260718))
		for sample := 0; sample < 6; sample++ {
			nVars := 2 + rng.Intn(3)
			var names []string
			for i := 0; i < nVars; i++ {
				names = append(names, fmt.Sprintf("V%d", i))
			}
			covered := map[int]bool{}
			for i := 0; i < nVars; i++ {
				if rng.Intn(2) == 0 {
					covered[i] = true
				}
			}
			wildcard := rng.Intn(4) == 0
			// Full coverage plus a wildcard makes the wildcard arm
			// unreachable (a hard error), so the oracle is an XOR.
			exhaustive := (len(covered) == nVars) != wildcard

			var b strings.Builder
			b.WriteString("package main\n\ntype E enum {\n")
			for _, n := range names {
				fmt.Fprintf(&b, "\t%s\n", n)
			}
			b.WriteString("}\n\nfunc classify(e E) int {\n\tout := -1\n\tmatch e {\n")
			for i, n := range names {
				if covered[i] {
					fmt.Fprintf(&b, "\tcase %s:\n\t\tout = %d\n", n, i)
				}
			}
			if wildcard {
				b.WriteString("\tcase _:\n\t\tout = 99\n")
			}
			b.WriteString("\t}\n\treturn out\n}\n\nfunc main() { _ = classify(V0{}) }\n")

			dir := filepath.Join(world.Dir, fmt.Sprintf("oracle%d", sample))
			if err := os.MkdirAll(dir, 0o755); err != nil {
				return err
			}
			if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte("module example.com/oracle\n\ngo 1.24\n"), 0o644); err != nil {
				return err
			}
			if err := os.WriteFile(filepath.Join(dir, "main.gp"), []byte(b.String()), 0o644); err != nil {
				return err
			}
			res, err := gen.Run(gen.Options{Dir: dir, Patterns: []string{"."}})
			if err != nil {
				return fmt.Errorf("sample %d: %v", sample, err)
			}
			// Degenerate all-covered-plus-wildcard cases still succeed; the
			// oracle is exact for exhaustiveness itself.
			if exhaustive != res.Ok() {
				return fmt.Errorf("sample %d: covered %d/%d wildcard=%v — gen Ok=%v, oracle says %v\ndiags: %v",
					sample, len(covered), nVars, wildcard, res.Ok(), exhaustive, res.Diags)
			}
			if res.Ok() {
				out, rerr := os.ReadFile(filepath.Join(dir, "main_gp.go"))
				if rerr != nil {
					return rerr
				}
				if strings.Contains(string(out), "//goplus:pattern") || strings.Contains(string(out), "case nil:") {
					return fmt.Errorf("sample %d: emitted file contains unresolved match artifacts", sample)
				}
			}
		}
		return nil
	})
}

// checkProperty runs a rapid property against the suite's testing.T,
// reporting falsification as a scenario failure.
func (w *World) checkProperty(prop func(*rapid.T)) error {
	failedBefore := w.T.Failed()
	rapid.Check(w.T, prop)
	if !failedBefore && w.T.Failed() {
		return fmt.Errorf("property falsified; counterexample in the test log")
	}
	return nil
}

var propDirCounter int

func (w *World) freshPropDir(rt *rapid.T) string {
	propDirCounter++
	dir := filepath.Join(w.Dir, fmt.Sprintf("prop%d", propDirCounter))
	if err := os.MkdirAll(dir, 0o755); err != nil {
		rt.Fatalf("mkdir: %v", err)
	}
	return dir
}

func mustWrite(rt *rapid.T, path, content string) {
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		rt.Fatalf("write %s: %v", path, err)
	}
}

func mustRead(rt *rapid.T, path string) string {
	b, err := os.ReadFile(path)
	if err != nil {
		rt.Fatalf("read %s: %v", path, err)
	}
	return string(b)
}

func mustGen(rt *rapid.T, dir string) *gen.Result {
	res, err := gen.Run(gen.Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		rt.Fatalf("gen.Run: %v", err)
	}
	if !res.Ok() {
		rt.Fatalf("gen diagnostics: %v", res.Diags)
	}
	return res
}
