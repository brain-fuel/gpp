package schedule

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestGrammarIndexAcrossPackageBoundary(t *testing.T) {
	tool := filepath.Join(t.TempDir(), "goplus")
	build := exec.Command("go", "build", "-o", tool, "./cmd/goplus")
	build.Dir = filepath.Join("..", "..")
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build Go+ tool: %v\n%s", err, out)
	}
	stdDir, err := filepath.Abs("..")
	if err != nil {
		t.Fatal(err)
	}

	compile := func(t *testing.T, source string) (string, error) {
		t.Helper()
		dir := t.TempDir()
		module := "module fixture\n\ngo 1.25.0\n\nrequire goforge.dev/goplus/std v0.0.0\nreplace goforge.dev/goplus/std => " + stdDir + "\n"
		if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte(module), 0o600); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, "main.gp"), []byte(source), 0o600); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command(tool, "gen", ".")
		cmd.Dir = dir
		out, err := cmd.CombinedOutput()
		return string(out), err
	}

	positive := "package main\nimport (\"time\"; \"goforge.dev/goplus/std/schedule\")\nfunc next(value schedule.Schedule[5]) { _ = schedule.NextStandard(value, time.Now()) }\nfunc main() {}\n"
	if out, err := compile(t, positive); err != nil {
		t.Fatalf("valid grammar-indexed use failed: %v\n%s", err, out)
	}
	negative := "package main\nimport (\"time\"; \"goforge.dev/goplus/std/schedule\")\nfunc next(value schedule.Schedule[5]) { _ = schedule.NextSeconds(value, time.Now()) }\nfunc main() {}\n"
	out, err := compile(t, negative)
	if err == nil {
		t.Fatalf("grammar mismatch unexpectedly compiled:\n%s", out)
	}
	if !strings.Contains(out, "requires Schedule[6], got Schedule[5]") {
		t.Fatalf("unexpected diagnostic: %s", out)
	}
}
