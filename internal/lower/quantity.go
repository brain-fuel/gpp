package lower

import (
	"goforge.dev/goplus/internal/syntax"
)

// Quantity pass 1 (v0.7.0): prefixes span [QPos, Name.Pos) and are
// deleted outright so the shadow Go never sees them. Usage checking and
// 0-param erasure are later-phase work. (`total` lowering lives with
// gen's total processing — the keyword is replaced by its marker line.)

// QuantityEdits strips one parameter's quantity prefix.
func QuantityEdits(f *syntax.File, q *syntax.QuantityParam) []Edit {
	return []Edit{{Start: f.Offset(q.QPos), End: f.Offset(q.Name.Pos()), New: ""}}
}
