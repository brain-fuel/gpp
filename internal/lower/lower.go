// Package lower computes and applies the text edits that turn G++ source
// into Go. Edits operate on original source bytes — the AST and type
// information decide where to edit, but bytes are the medium, so untouched
// regions (comments, formatting) pass through losslessly.
package lower

import (
	"fmt"
	"sort"
	"strings"

	"goforge.dev/gpp/internal/syntax"
)

// Edit replaces src[Start:End] with New. A zero-width edit (Start == End)
// is an insertion.
type Edit struct {
	Start, End int
	New        string
}

// Apply applies edits to src. Edits must be non-overlapping; they may be
// given in any order. Insertions at the same offset are applied in the
// order given.
func Apply(src []byte, edits []Edit) ([]byte, error) {
	sorted := make([]Edit, len(edits))
	copy(sorted, edits)
	sort.SliceStable(sorted, func(i, j int) bool { return sorted[i].Start < sorted[j].Start })
	var out []byte
	prev := 0
	for _, e := range sorted {
		if e.Start < prev || e.End < e.Start || e.End > len(src) {
			return nil, fmt.Errorf("internal error: overlapping or out-of-range edit [%d,%d) (previous end %d, len %d)",
				e.Start, e.End, prev, len(src))
		}
		out = append(out, src[prev:e.Start]...)
		out = append(out, e.New...)
		prev = e.End
	}
	out = append(out, src[prev:]...)
	return out, nil
}

// TParam is a resolved receiver type parameter: its name as written on the
// receiver and its constraint (rendered in receiver-name terms).
type TParam struct {
	Name       string
	Constraint string
}

// Decl computes the edits lowering one generic method declaration to a
// package-level function declaration named funcName:
//
//	func (s Stack[T]) Map[U any](f func(T) U) Stack[U] { … }
//	→ func StackMap[T any, U any](s Stack[T], f func(T) U) Stack[U] { … }
//
// The body is untouched: the receiver keeps its name, now as the first
// parameter.
func Decl(f *syntax.File, gm *syntax.GenericMethod, funcName string, recvTParams []TParam) []Edit {
	fd := gm.Decl
	var edits []Edit

	// "(s Stack[T]) Map" -> "StackMap"
	edits = append(edits, Edit{
		Start: f.Offset(fd.Recv.Opening),
		End:   f.Offset(fd.Name.End()),
		New:   funcName,
	})

	// "[U any]" -> "[T any, U any]" — insert receiver tparams (with
	// constraints) before the method's own, preserved verbatim. A method
	// with no type parameters of its own (an enum method) gains a fresh
	// bracket list when its receiver is generic.
	if len(recvTParams) > 0 {
		parts := make([]string, len(recvTParams))
		for i, tp := range recvTParams {
			parts[i] = tp.Name + " " + tp.Constraint
		}
		if fd.Type.TypeParams != nil {
			edits = append(edits, Edit{
				Start: gm.LBrack + 1,
				End:   gm.LBrack + 1,
				New:   strings.Join(parts, ", ") + ", ",
			})
		} else {
			at := f.Offset(fd.Name.End())
			edits = append(edits, Edit{
				Start: at,
				End:   at,
				New:   "[" + strings.Join(parts, ", ") + "]",
			})
		}
	}

	// "(f func(T) U)" -> "(s Stack[T], f func(T) U)"
	recvField := fd.Recv.List[0]
	recvName := gm.RecvName
	if recvName == "" {
		recvName = "_"
	}
	recvType := string(f.Src[f.Offset(recvField.Type.Pos()):f.Offset(recvField.Type.End())])
	insert := recvName + " " + recvType
	if fd.Type.Params != nil && len(fd.Type.Params.List) > 0 {
		insert += ", "
	}
	lparen := f.Offset(fd.Type.Params.Opening)
	edits = append(edits, Edit{Start: lparen + 1, End: lparen + 1, New: insert})

	return edits
}

// MarkerInsert computes the edit inserting a marker comment line directly
// above a method's declaration (above its doc comment, if any).
func MarkerInsert(f *syntax.File, gm *syntax.GenericMethod, marker string) Edit {
	pos := gm.Decl.Pos()
	if gm.Decl.Doc != nil {
		pos = gm.Decl.Doc.Pos()
	}
	off := f.Offset(pos)
	for off > 0 && f.Src[off-1] != '\n' {
		off--
	}
	return Edit{Start: off, End: off, New: marker + "\n"}
}
