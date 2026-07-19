package lower

import (
	"goforge.dev/gpp/internal/syntax"
)

// Quantity + totality pass 1 (v0.7.0). The shadow Go must not see either
// spelling: quantity prefixes span [QPos, Name.Pos) and are deleted
// outright; `total` is deleted from the keyword through the following
// whitespace. Checking (termination, usage, erasure of 0-params) is
// later-phase work — pass 1 only makes the claims invisible to Go.

// QuantityEdits strips one parameter's quantity prefix.
func QuantityEdits(f *syntax.File, q *syntax.QuantityParam) []Edit {
	return []Edit{{Start: f.Offset(q.QPos), End: f.Offset(q.Name.Pos()), New: ""}}
}

// TotalEdits strips one `total` keyword.
func TotalEdits(f *syntax.File, t *syntax.TotalFunc) []Edit {
	start := f.Offset(t.TotalPos)
	end := start + len("total")
	for end < len(f.Src) && (f.Src[end] == ' ' || f.Src[end] == '\t') {
		end++
	}
	return []Edit{{Start: start, End: end, New: ""}}
}
