package lower

import (
	"fmt"

	"goforge.dev/gpp/internal/syntax"
)

// PatternCarrier is the comment prefix threading pattern structure through
// the resolution fixpoint. The resolver deletes each carrier as it expands
// the arm — the fixpoint's progress signal for matches.
const PatternCarrier = "//gpp:pattern "

// MatchSkeleton lowers one match statement to a parseable Go type switch
// carrying its patterns as comments. Edits are surgical — the match header
// and each case header only — so nested matches inside arm bodies edit
// independently without overlap:
//
//	match s {              →  switch __gpp_m0 := any(s).(type) {
//	case Circle(r):        →  case nil:
//	                          //gpp:pattern Circle(r)
//		<body verbatim>           <body verbatim>
//	}                      →  }
//
// The scrutinee goes through any(): a GADT variant's ground marker method
// makes a direct type switch on Expr[T] an "impossible case" compile error
// inside generic code, and the sealed default-panic arm keeps the erasure
// safe regardless.
func MatchSkeleton(f *syntax.File, m *syntax.MatchStmt, index int) []Edit {
	var edits []Edit
	subj := string(f.Src[f.Offset(m.Subject.Pos()):f.Offset(m.Subject.End())])
	edits = append(edits, Edit{
		Start: f.Offset(m.Match),
		End:   f.Offset(m.Lbrace) + 1,
		New:   fmt.Sprintf("switch __gpp_m%d := any(%s).(type) {", index, subj),
	})
	for _, c := range m.Cases {
		patStart := c.Pattern.Pos()
		if c.Binder != nil {
			patStart = c.Binder.Pos()
		}
		pattern := string(f.Src[f.Offset(patStart):f.Offset(c.Colon)])
		edits = append(edits, Edit{
			Start: f.Offset(c.Case),
			End:   f.Offset(c.Colon) + 1,
			New:   "case nil:\n" + PatternCarrier + pattern,
		})
	}
	return edits
}
