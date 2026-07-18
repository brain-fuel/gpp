// Package diag defines gpp's user-facing diagnostics.
package diag

import (
	"fmt"
	"go/token"
	"io"
	"sort"
)

// Diagnostic is one user-facing error, positioned in .gpp source when
// attributable.
type Diagnostic struct {
	Pos token.Position // zero value when the diagnostic has no position
	Msg string
}

func (d Diagnostic) String() string {
	if d.Pos.Filename == "" && d.Pos.Line == 0 {
		return d.Msg
	}
	return fmt.Sprintf("%s: %s", d.Pos, d.Msg)
}

// Errorf builds an unpositioned diagnostic.
func Errorf(format string, args ...any) Diagnostic {
	return Diagnostic{Msg: fmt.Sprintf(format, args...)}
}

// At builds a positioned diagnostic.
func At(pos token.Position, format string, args ...any) Diagnostic {
	return Diagnostic{Pos: pos, Msg: fmt.Sprintf(format, args...)}
}

// Sort orders diagnostics by file, line, column, then message, and removes
// exact duplicates.
func Sort(ds []Diagnostic) []Diagnostic {
	sort.Slice(ds, func(i, j int) bool {
		a, b := ds[i], ds[j]
		if a.Pos.Filename != b.Pos.Filename {
			return a.Pos.Filename < b.Pos.Filename
		}
		if a.Pos.Line != b.Pos.Line {
			return a.Pos.Line < b.Pos.Line
		}
		if a.Pos.Column != b.Pos.Column {
			return a.Pos.Column < b.Pos.Column
		}
		return a.Msg < b.Msg
	})
	out := ds[:0]
	for i, d := range ds {
		if i == 0 || d != ds[i-1] {
			out = append(out, d)
		}
	}
	return out
}

// Render writes diagnostics one per line.
func Render(w io.Writer, ds []Diagnostic) {
	for _, d := range ds {
		fmt.Fprintln(w, d.String())
	}
}
