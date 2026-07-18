package bddtest

import (
	"fmt"
	"go/parser"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"strings"

	"github.com/cucumber/godog"

	"goforge.dev/gpp/internal/emit"
	"goforge.dev/gpp/internal/gen"
)

type genState struct {
	snapshot map[string]string // generated files at "record" time
	context  string            // package context for the corpus step
}

func initGenSteps(sc *godog.ScenarioContext, w func() *World, gs *genState) {
	sc.Step(`^the file "([^"]+)" contains:$`, func(name string, doc *godog.DocString) error {
		got, err := w().readFile(name)
		if err != nil {
			return err
		}
		if !strings.Contains(got, doc.Content) {
			return fmt.Errorf("%s does not contain:\n%s\n\nfull content:\n%s", name, doc.Content, got)
		}
		return nil
	})

	sc.Step(`^the file "([^"]+)" does not exist$`, func(name string) error {
		path := filepath.Join(w().Dir, filepath.FromSlash(name))
		if _, err := os.Stat(path); err == nil {
			return fmt.Errorf("%s exists, expected absence", name)
		}
		return nil
	})

	sc.Step(`^the file "([^"]+)" is valid Go$`, func(name string) error {
		got, err := w().readFile(name)
		if err != nil {
			return err
		}
		_, err = parser.ParseFile(token.NewFileSet(), name, []byte(got), parser.SkipObjectResolution)
		if err != nil {
			return fmt.Errorf("%s is not valid Go: %v", name, err)
		}
		return nil
	})

	sc.Step(`^the file "([^"]+)" is exactly the header for "([^"]+)" plus the source$`, func(name, gppName string) error {
		world := w()
		got, err := world.readFile(name)
		if err != nil {
			return err
		}
		src, err := world.readFile(gppName)
		if err != nil {
			return err
		}
		want, err := emit.Finish(gppName, []byte(src))
		if err != nil {
			return err
		}
		if got != string(want) {
			return fmt.Errorf("%s differs from header+source passthrough:\ngot:\n%s\nwant:\n%s", name, got, want)
		}
		return nil
	})

	sc.Step(`^I record the generated files$`, func() error {
		snap, err := generatedFiles(w().Dir)
		if err != nil {
			return err
		}
		gs.snapshot = snap
		return nil
	})

	sc.Step(`^the generated files are unchanged$`, func() error {
		now, err := generatedFiles(w().Dir)
		if err != nil {
			return err
		}
		if len(now) != len(gs.snapshot) {
			return fmt.Errorf("generated file set changed: had %d, now %d", len(gs.snapshot), len(now))
		}
		for name, content := range gs.snapshot {
			if now[name] != content {
				return fmt.Errorf("%s changed between runs", name)
			}
		}
		return nil
	})

	sc.Step(`^running gpp with arguments "([^"]*)" exits with (\d+)$`, func(args string, want int) error {
		world := w()
		if err := world.runGpp(splitArgs(args)); err != nil {
			return err
		}
		if world.ExitCode != want {
			return fmt.Errorf("exit code = %d, want %d\nstderr:\n%s", world.ExitCode, want, world.Stderr.String())
		}
		return nil
	})

	sc.Step(`^the package context:$`, func(doc *godog.DocString) error {
		gs.context = doc.Content
		return nil
	})

	sc.Step(`^these methods lower to these functions:$`, func(table *godog.Table) error {
		world := w()
		if len(table.Rows) < 2 {
			return fmt.Errorf("expected a header row and at least one data row")
		}
		for i, row := range table.Rows[1:] {
			method := strings.TrimSpace(row.Cells[0].Value)
			wantFunc := strings.TrimSpace(row.Cells[1].Value)
			dir := filepath.Join(world.Dir, fmt.Sprintf("corpus%d", i))
			if err := os.MkdirAll(dir, 0o755); err != nil {
				return err
			}
			src := "package corpus\n\n" + gs.context + "\n\n" + method + " {\n\tpanic(\"corpus\")\n}\n"
			if err := os.WriteFile(filepath.Join(dir, "in.gpp"), []byte(src), 0o644); err != nil {
				return err
			}
			res, err := gen.Run(gen.Options{Dir: dir, Patterns: []string{"."}})
			if err != nil {
				return fmt.Errorf("row %d (%s): %v", i+1, method, err)
			}
			if !res.Ok() {
				return fmt.Errorf("row %d (%s): diagnostics: %v", i+1, method, res.Diags)
			}
			out, err := os.ReadFile(filepath.Join(dir, "in_gpp.go"))
			if err != nil {
				return err
			}
			if !strings.Contains(string(out), wantFunc+" {") {
				return fmt.Errorf("row %d: emitted output for\n  %s\ndoes not contain\n  %s\ngot:\n%s",
					i+1, method, wantFunc, out)
			}
		}
		return nil
	})
}

// generatedFiles maps relative path -> content for every *_gpp.go under dir.
func generatedFiles(dir string) (map[string]string, error) {
	out := map[string]string{}
	err := filepath.WalkDir(dir, func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || !strings.HasSuffix(path, emit.GeneratedSuffix) {
			return err
		}
		content, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(dir, path)
		out[rel] = string(content)
		return nil
	})
	return out, err
}
