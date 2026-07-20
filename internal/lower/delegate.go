package lower

import (
	"goforge.dev/goplus/internal/directive"
	"goforge.dev/goplus/internal/syntax"
)

// Delegation pass 1 (v0.6.0). The trailing `delegate` keyword is stripped
// (the shadow struct is plain Go) and a //goplus:delegate marker line lands
// above the field; resolution generates the forwarders once the field's
// interface type is known.

// DelegateEdits lowers one delegate field.
func DelegateEdits(f *syntax.File, d *syntax.DelegateField) []Edit {
	var edits []Edit

	// Marker line above the field.
	at := f.Offset(d.Field.Pos())
	if d.Field.Doc != nil {
		at = f.Offset(d.Field.Doc.Pos())
	}
	for at > 0 && f.Src[at-1] != '\n' {
		at--
	}
	edits = append(edits, Edit{Start: at, End: at, New: directive.DelegatePrefix + "\n"})

	// Strip ` delegate` (the keyword plus its preceding space).
	start := f.Offset(d.DelegatePos)
	for start > 0 && (f.Src[start-1] == ' ' || f.Src[start-1] == '\t') {
		start--
	}
	edits = append(edits, Edit{Start: start, End: f.Offset(d.DelegatePos) + len("delegate"), New: ""})
	return edits
}
