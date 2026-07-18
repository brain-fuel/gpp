package bddtest

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/cucumber/godog"

	"goforge.dev/gpp/internal/cli"
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

	sc.Step(`^I run gpp with arguments "([^"]*)"$`, func(args string) error {
		return w.runGpp(splitArgs(args))
	})
	sc.Step(`^I run gpp in "([^"]+)" with arguments "([^"]*)"$`, func(sub, args string) error {
		return w.runGppIn(sub, splitArgs(args))
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
	sc.Step(`^a file "([^"]+)":$`, func(name string, doc *godog.DocString) error {
		return w.writeFile(name, doc.Content)
	})
}

// runGpp invokes the CLI in-process with the scenario dir as working directory.
func (w *World) runGpp(args []string) error {
	return w.runGppIn(".", args)
}

func (w *World) runGppIn(sub string, args []string) error {
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
