package gen

import (
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// expandPatterns resolves go-style package patterns ("./...", ".", "./pkg",
// "pkg/...") to directories under root, following the go tool's convention
// of skipping vendor, testdata, and dot/underscore-prefixed directories.
func expandPatterns(root string, patterns []string) ([]string, error) {
	if len(patterns) == 0 {
		patterns = []string{"./..."}
	}
	seen := map[string]bool{}
	var dirs []string
	add := func(dir string) {
		if !seen[dir] {
			seen[dir] = true
			dirs = append(dirs, dir)
		}
	}
	for _, pat := range patterns {
		pat = filepath.ToSlash(pat)
		base, recursive := strings.CutSuffix(pat, "...")
		if r, ok := strings.CutSuffix(base, "/"); ok && recursive {
			base = r
		}
		if base == "" {
			base = "."
		}
		start := filepath.Join(root, filepath.FromSlash(base))
		info, err := os.Stat(start)
		if err != nil || !info.IsDir() {
			return nil, fmt.Errorf("pattern %q: no such directory", pat)
		}
		if !recursive {
			add(start)
			continue
		}
		err = filepath.WalkDir(start, func(path string, d fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if !d.IsDir() {
				return nil
			}
			name := d.Name()
			if path != start && (name == "vendor" || name == "testdata" ||
				strings.HasPrefix(name, ".") || strings.HasPrefix(name, "_")) {
				return fs.SkipDir
			}
			add(path)
			return nil
		})
		if err != nil {
			return nil, err
		}
	}
	sort.Strings(dirs)
	return dirs, nil
}

// modulePath reads the module path from the go.mod at or above dir; it
// returns "" when no go.mod is found (package paths then fall back to
// directory names).
func modulePath(dir string) (path, moduleRoot string) {
	for {
		data, err := os.ReadFile(filepath.Join(dir, "go.mod"))
		if err == nil {
			for _, line := range strings.Split(string(data), "\n") {
				line = strings.TrimSpace(line)
				if rest, ok := strings.CutPrefix(line, "module"); ok {
					return strings.TrimSpace(strings.TrimSuffix(rest, "// indirect")), dir
				}
			}
			return "", dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return "", ""
		}
		dir = parent
	}
}
