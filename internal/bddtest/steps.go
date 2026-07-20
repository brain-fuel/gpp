package bddtest

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/cucumber/godog"

	"goforge.dev/goplus/internal/cli"
)

// InitializeScenario registers every step definition against a fresh World.
func InitializeScenario(t *testing.T, sc *godog.ScenarioContext) {
	var w *World
	ps := &parseState{}
	ns := &namingState{}
	gs := &genState{}

	sc.Before(func(ctx context.Context, _ *godog.Scenario) (context.Context, error) {
		*ps = parseState{}
		*ns = namingState{}
		*gs = genState{}
		var err error
		w, err = newWorld(t)
		return ctx, err
	})
	initParsingSteps(sc, func() *World { return w }, ps)
	initParsingV2Steps(sc, ps)
	initParsingV3Steps(sc, ps)
	initParsingV4Steps(sc, ps)
	initParsingV5Steps(sc, ps)
	initNamingSteps(sc, func() *World { return w }, ns)
	initGenSteps(sc, func() *World { return w }, gs)
	initGitSteps(sc, func() *World { return w })
	initPropertySteps(sc, func() *World { return w })
	sc.After(func(ctx context.Context, _ *godog.Scenario, _ error) (context.Context, error) {
		if w != nil {
			w.cleanup()
		}
		return ctx, nil
	})

	sc.Step(`^I run goplus with arguments "([^"]*)"$`, func(args string) error {
		return w.runGoplus(splitArgs(args))
	})
	sc.Step(`^I run goplus in "([^"]+)" with arguments "([^"]*)"$`, func(sub, args string) error {
		return w.runGoplusIn(sub, splitArgs(args))
	})
	sc.Step(`^the file "([^"]+)" is deleted$`, func(name string) error {
		return os.Remove(filepath.Join(w.Dir, filepath.FromSlash(name)))
	})
	sc.Step(`^the exit code is (\d+)$`, func(want int) error {
		if w.ExitCode != want {
			return fmt.Errorf("exit code = %d, want %d\nstdout:\n%s\nstderr:\n%s",
				w.ExitCode, want, w.Stdout.String(), w.Stderr.String())
		}
		return nil
	})
	sc.Step(`^(stdout|stderr) contains "([^"]*)"$`, func(stream, want string) error {
		got := w.Stdout.String()
		if stream == "stderr" {
			got = w.Stderr.String()
		}
		if !strings.Contains(got, want) {
			return fmt.Errorf("%s does not contain %q; got:\n%s", stream, want, got)
		}
		return nil
	})
	sc.Step(`^(stdout|stderr) contains:$`, func(stream string, doc *godog.DocString) error {
		got := w.Stdout.String()
		if stream == "stderr" {
			got = w.Stderr.String()
		}
		if !strings.Contains(got, doc.Content) {
			return fmt.Errorf("%s does not contain:\n%s\ngot:\n%s", stream, doc.Content, got)
		}
		return nil
	})
	sc.Step(`^a file "([^"]+)":$`, func(name string, doc *godog.DocString) error {
		return w.writeFile(name, doc.Content)
	})
	// A go.mod that requires goforge.dev/goplus/std, replaced by this repo's
	// std directory — the scenario-side equivalent of a released std.
	sc.Step(`^a module "([^"]+)" using the goplus standard library$`, func(mod string) error {
		content := fmt.Sprintf(
			"module %s\n\ngo 1.24\n\nrequire goforge.dev/goplus/std v0.0.0\n\nreplace goforge.dev/goplus/std => %s\n",
			mod, filepath.Join(w.origWD, "std"))
		return w.writeFile("go.mod", content)
	})
	// A go.mod that requires rapid (for generated law tests), replaced by
	// the repo's module-cache copy so scenarios stay offline.
	sc.Step(`^a module "([^"]+)" using rapid for law tests$`, func(mod string) error {
		out, err := exec.Command("go", "list", "-m", "-f", "{{.Dir}}", "pgregory.net/rapid").Output()
		if err != nil {
			return fmt.Errorf("locating rapid in the module cache: %v", err)
		}
		dir := strings.TrimSpace(string(out))
		content := fmt.Sprintf(
			"module %s\n\ngo 1.24\n\nrequire pgregory.net/rapid v1.3.0\n\nreplace pgregory.net/rapid => %s\n",
			mod, dir)
		return w.writeFile("go.mod", content)
	})
}

// runGoplus invokes the CLI in-process with the scenario dir as working directory.
func (w *World) runGoplus(args []string) error {
	return w.runGoplusIn(".", args)
}

func (w *World) runGoplusIn(sub string, args []string) error {
	w.Stdout.Reset()
	w.Stderr.Reset()
	if err := os.Chdir(filepath.Join(w.Dir, filepath.FromSlash(sub))); err != nil {
		return err
	}
	defer os.Chdir(w.origWD)
	w.ExitCode = cli.Run(args, &w.Stdout, &w.Stderr)
	return nil
}

// splitArgs splits a step's argument string on whitespace, honoring single
// quotes for arguments that contain spaces.
func splitArgs(s string) []string {
	var out []string
	var cur strings.Builder
	inQuote := false
	for _, r := range s {
		switch {
		case r == '\'':
			inQuote = !inQuote
		case !inQuote && (r == ' ' || r == '\t'):
			if cur.Len() > 0 {
				out = append(out, cur.String())
				cur.Reset()
			}
		default:
			cur.WriteRune(r)
		}
	}
	if cur.Len() > 0 {
		out = append(out, cur.String())
	}
	return out
}
