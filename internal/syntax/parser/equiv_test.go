package parser_test

// The vendored fork must behave byte-for-byte like stock go/parser on pure
// Go source: identical ASTs, identical error lists. This test is the drift
// detector for toolchain re-vendors and the safety net under every goplus
// grammar hook (which may only ever claim syntax that is invalid Go).

import (
	"go/ast"
	stdparser "go/parser"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"reflect"
	"runtime"
	"strings"
	"testing"

	forkparser "goforge.dev/goplus/internal/syntax/parser"
)

func corpus(t *testing.T) []string {
	var files []string
	add := func(root string, limit int) {
		n := 0
		filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
			if err != nil || d.IsDir() || !strings.HasSuffix(path, ".go") {
				return nil
			}
			if limit > 0 && n >= limit {
				return fs.SkipAll
			}
			n++
			files = append(files, path)
			return nil
		})
	}
	// This repo (every package, including tests).
	add("../../..", 0)
	// A grammar-rich GOROOT sample.
	add(filepath.Join(runtime.GOROOT(), "src", "go", "types"), 150)
	add(filepath.Join(runtime.GOROOT(), "src", "fmt"), 50)
	if len(files) < 20 {
		t.Fatalf("corpus too small: %d files", len(files))
	}
	return files
}

func TestForkEquivalence(t *testing.T) {
	mode := stdparser.ParseComments | stdparser.SkipObjectResolution
	for _, path := range corpus(t) {
		src, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		stockFset := token.NewFileSet()
		stockAST, stockErr := stdparser.ParseFile(stockFset, path, src, mode)
		forkFset := token.NewFileSet()
		forkAST, forkExt, forkErr := forkparser.ParseFileExt(forkFset, path, src, forkparser.Mode(mode))

		if (stockErr == nil) != (forkErr == nil) {
			t.Errorf("%s: error mismatch:\nstock: %v\nfork:  %v", path, stockErr, forkErr)
			continue
		}
		if stockErr != nil && stockErr.Error() != forkErr.Error() {
			t.Errorf("%s: error text mismatch:\nstock: %v\nfork:  %v", path, stockErr, forkErr)
			continue
		}
		if forkExt != nil && (len(forkExt.Enums) > 0 || len(forkExt.Matches) > 0 ||
			len(forkExt.Classes) > 0 || len(forkExt.Instances) > 0) {
			t.Errorf("%s: pure Go produced extensions: %d enums, %d matches, %d classes, %d instances",
				path, len(forkExt.Enums), len(forkExt.Matches), len(forkExt.Classes), len(forkExt.Instances))
		}
		if !reflect.DeepEqual(normalize(stockAST), normalize(forkAST)) {
			t.Errorf("%s: AST mismatch", path)
		}
	}
}

// normalize strips fields that legitimately differ between the two parsers
// (none today; kept as an extension point for future toolchain quirks).
func normalize(f *ast.File) *ast.File { return f }
