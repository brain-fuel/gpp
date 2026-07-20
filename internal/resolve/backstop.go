package resolve

import (
	"go/token"
	"strconv"
	"strings"

	"golang.org/x/tools/go/packages"

	"goforge.dev/goplus/internal/diag"
	"goforge.dev/goplus/internal/sourcemap"
)

// Backstop type-checks the final emitted texts strictly and returns every
// error, remapped into .gp positions where the error lies in a generated
// file. This is the full go/types safety net behind the targeted
// resolution pass: anything the lowering got wrong, and any ordinary type
// error the user wrote, surfaces here exactly once — before anything is
// written to disk.
func Backstop(in *Input, maps map[string]*sourcemap.Map) ([]diag.Diagnostic, error) {
	cfg := &packages.Config{
		Mode: packages.NeedName | packages.NeedFiles | packages.NeedCompiledGoFiles |
			packages.NeedImports | packages.NeedDeps | packages.NeedTypes |
			packages.NeedSyntax | packages.NeedTypesInfo,
		Dir:     in.Dir,
		Overlay: in.Texts,
	}
	pkgs, err := packages.Load(cfg, in.Patterns...)
	if err != nil {
		return nil, err
	}
	var diags []diag.Diagnostic
	seen := map[string]bool{}
	for _, pkg := range pkgs {
		for _, perr := range pkg.Errors {
			pos := parsePos(perr.Pos)
			msg := perr.Msg
			if m, ok := maps[pos.Filename]; ok {
				if mapped, ok := m.Map(pos); ok {
					pos = mapped
				} else {
					msg = "goplus internal lowering error (please report): " + msg
				}
			}
			d := diag.At(pos, "%s", msg)
			if !seen[d.String()] {
				seen[d.String()] = true
				diags = append(diags, d)
			}
		}
	}
	return diags, nil
}

// parsePos parses a go/packages error position ("file:line:col",
// "file:line", or "-"), tolerating Windows drive letters.
func parsePos(s string) token.Position {
	if s == "" || s == "-" {
		return token.Position{}
	}
	rest := s
	var col, line int
	if i := strings.LastIndex(rest, ":"); i > 1 {
		if n, err := strconv.Atoi(rest[i+1:]); err == nil {
			col = n
			rest = rest[:i]
		}
	}
	if i := strings.LastIndex(rest, ":"); i > 1 {
		if n, err := strconv.Atoi(rest[i+1:]); err == nil {
			line = n
			rest = rest[:i]
		}
	}
	if line == 0 {
		line, col = col, 0
	}
	return token.Position{Filename: rest, Line: line, Column: col}
}
