package gen

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestLawTypeImports(t *testing.T) {
	dir := t.TempDir()
	src := filepath.Join(dir, "laws.gp")
	text := "package p\nimport (\n\t\"example.com/model/schema\"\n\tx \"example.com/xpkg\"\n)\n"
	if err := os.WriteFile(src, []byte(text), 0o600); err != nil {
		t.Fatal(err)
	}
	got := lawTypeImports(src, "rapid.Make[schema.Package]()\nvar _ x.Value", "example.com/p")
	for _, want := range []string{"\"example.com/model/schema\"", "x \"example.com/xpkg\""} {
		if !strings.Contains(got, want) {
			t.Fatalf("missing %s in %q", want, got)
		}
	}
}

func TestLawTypeImportsFromSingleImport(t *testing.T) {
	dir := t.TempDir()
	src := filepath.Join(dir, "laws.gp")
	if err := os.WriteFile(src, []byte("package p\nimport \"example.com/model/schema\"\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	got := lawTypeImports(src, "rapid.Make[schema.Package]()", "example.com/p")
	if !strings.Contains(got, "\"example.com/model/schema\"") {
		t.Fatalf("single import missing in %q", got)
	}
}
