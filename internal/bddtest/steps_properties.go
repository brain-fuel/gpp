package bddtest

import (
	"fmt"
	"go/token"
	"os"
	"path/filepath"
	"strings"

	"github.com/cucumber/godog"
	"pgregory.net/rapid"

	"goforge.dev/gpp/internal/emit"
	"goforge.dev/gpp/internal/gen"
	"goforge.dev/gpp/internal/syntax"
)

func initPropertySteps(sc *godog.ScenarioContext, w func() *World) {
	sc.Step(`^for any plain Go file, parsing as G\+\+ succeeds with no generic methods$`, func() error {
		return w().checkProperty(func(rt *rapid.T) {
			src := plainGoSource(rt)
			f, err := syntax.ParseFile(token.NewFileSet(), "prop.gpp", []byte(src))
			if err != nil {
				rt.Fatalf("valid Go rejected by the G++ frontend: %v\n%s", err, src)
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
			mustWrite(rt, filepath.Join(dir, "in.gpp"), src)
			res := mustGen(rt, dir)
			_ = res
			got := mustRead(rt, filepath.Join(dir, "in_gpp.go"))
			want := emit.Header("in.gpp") + src
			if got != want {
				rt.Fatalf("passthrough not lossless:\n--- got ---\n%s\n--- want ---\n%s", got, want)
			}
		})
	})

	sc.Step(`^for any G\+\+ package, generating twice produces identical bytes and no rewrites$`, func() error {
		world := w()
		return world.checkProperty(func(rt *rapid.T) {
			p := gppPackageGen(rt)
			dir := world.freshPropDir(rt)
			mustWrite(rt, filepath.Join(dir, "in.gpp"), p.Source(nil))
			mustGen(rt, dir)
			first := mustRead(rt, filepath.Join(dir, "in_gpp.go"))
			res := mustGen(rt, dir)
			if len(res.Written) != 0 {
				rt.Fatalf("second gen rewrote files: %v", res.Written)
			}
			second := mustRead(rt, filepath.Join(dir, "in_gpp.go"))
			if first != second {
				rt.Fatalf("output changed between identical runs")
			}
		})
	})

	sc.Step(`^for any G\+\+ package, permuting declarations preserves the lowered function names$`, func() error {
		world := w()
		return world.checkProperty(func(rt *rapid.T) {
			p := gppPackageGen(rt)
			order := permutation(rt, len(p.Decls))

			dirA := world.freshPropDir(rt)
			dirB := world.freshPropDir(rt)
			mustWrite(rt, filepath.Join(dirA, "in.gpp"), p.Source(nil))
			mustWrite(rt, filepath.Join(dirB, "in.gpp"), p.Source(order))
			mustGen(rt, dirA)
			mustGen(rt, dirB)
			outA := mustRead(rt, filepath.Join(dirA, "in_gpp.go"))
			outB := mustRead(rt, filepath.Join(dirB, "in_gpp.go"))
			for _, name := range p.MethodNames {
				needle := "func " + name + "["
				if !strings.Contains(outA, needle) {
					rt.Fatalf("expected lowered name %s missing from original order:\n%s", name, outA)
				}
				if !strings.Contains(outB, needle) {
					rt.Fatalf("expected lowered name %s missing from permuted order:\n%s", name, outB)
				}
			}
		})
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
