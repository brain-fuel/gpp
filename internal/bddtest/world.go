// Package bddtest hosts the Godog step definitions and per-scenario World for
// the goplus spec suite. The feature files under features/ plus the grammar under
// spec/ are the authoritative specification of goplus behavior.
package bddtest

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// World is the isolated state of one scenario: a temp directory acting as the
// user's module, plus the outcome of the last goplus invocation.
type World struct {
	// T is the suite-level testing.T, needed by property-based steps that
	// drive pgregory.net/rapid.
	T *testing.T

	// Dir is the scenario's working directory (a fresh temp dir).
	Dir string

	Stdout   bytes.Buffer
	Stderr   bytes.Buffer
	ExitCode int

	// LastGoplusFile is the most recently written Go+ fixture file, the
	// implicit subject of frontend steps like "I parse it".
	LastGoplusFile string

	origWD string
}

func newWorld(t *testing.T) (*World, error) {
	dir, err := os.MkdirTemp("", "goplus-scenario-*")
	if err != nil {
		return nil, err
	}
	// Resolve symlinks (macOS /var -> /private/var) so paths reported by
	// tools match paths we compare against.
	dir, err = filepath.EvalSymlinks(dir)
	if err != nil {
		return nil, err
	}
	wd, err := os.Getwd()
	if err != nil {
		return nil, err
	}
	return &World{T: t, Dir: dir, origWD: wd}, nil
}

func (w *World) cleanup() {
	_ = os.Chdir(w.origWD)
	_ = os.RemoveAll(w.Dir)
}

// writeFile writes a scenario fixture file under w.Dir, creating parents.
func (w *World) writeFile(name, content string) error {
	path := filepath.Join(w.Dir, filepath.FromSlash(name))
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	if !strings.HasSuffix(content, "\n") {
		content += "\n"
	}
	return os.WriteFile(path, []byte(content), 0o644)
}

func (w *World) readFile(name string) (string, error) {
	b, err := os.ReadFile(filepath.Join(w.Dir, filepath.FromSlash(name)))
	return string(b), err
}
