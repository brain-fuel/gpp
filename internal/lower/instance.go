package lower

import (
	"go/ast"
	"strconv"

	"goforge.dev/goplus/internal/directive"
	"goforge.dev/goplus/internal/syntax"
)

// Instance lowering (v0.5.0). An instance becomes a package value built by
// a constructor over a heap witness, so member closures see the COMPLETED
// witness (defaults filled by pass 2, mutual reference allowed). Member
// bodies stay byte-in-place:
//
//	instance IntAdd Group[int] {        //goplus:instance IntAdd Group[int]
//		Combine(a, b int) int { … }     var IntAdd = func() Group[int] {
//		…                           ⇒   	w := &Group[int]{
//	}                                   		Combine: func(a, b int) int { … },
//	                                    		…
//	                                    	}
//	                                    	return *w
//	                                    }()
//
// Generic instances lower to functions (vars cannot be generic).

// InstanceEdits lowers one instance declaration.
func InstanceEdits(f *syntax.File, d *syntax.InstanceDecl) []Edit {
	classText := string(f.Src[f.Offset(d.Class.Pos()):f.Offset(d.Class.End())])
	w := freshName(f, d.InstancePos, d.Rbrace, "w")

	var edits []Edit

	// Marker above the declaration.
	tparamsSrc := ""
	if d.TParams != nil {
		tparamsSrc = string(f.Src[f.Offset(d.TParams.Opening)+1 : f.Offset(d.TParams.Closing)])
	}
	marker := directive.InstanceMarker{Name: d.Name.Name, TParams: tparamsSrc, Class: instanceClassRef(f, d.Class)}
	at := f.Offset(d.InstancePos)
	if d.Doc != nil {
		at = f.Offset(d.Doc.Pos())
	}
	for at > 0 && f.Src[at-1] != '\n' {
		at--
	}
	edits = append(edits, Edit{Start: at, End: at, New: marker.String() + "\n"})

	// Head.
	if d.TParams == nil {
		// `instance IntAdd ` → `var IntAdd = func() `.
		edits = append(edits, Edit{Start: f.Offset(d.InstancePos), End: f.Offset(d.Name.Pos()), New: "var "})
		edits = append(edits, Edit{Start: f.Offset(d.Name.End()), End: f.Offset(d.Name.End()), New: " = func()"})
	} else {
		// `instance SliceConcat[T any] ` → `func SliceConcat[T any]() `.
		edits = append(edits, Edit{Start: f.Offset(d.InstancePos), End: f.Offset(d.Name.Pos()), New: "func "})
		closing := f.Offset(d.TParams.Closing) + 1
		edits = append(edits, Edit{Start: closing, End: closing, New: "()"})
	}
	edits = append(edits, Edit{
		Start: f.Offset(d.Lbrace),
		End:   f.Offset(d.Lbrace) + 1,
		New:   "{\n" + w + " := &" + classText + "{",
	})

	// Members: `Combine(a, b int) int { … }` → `Combine: func(a, b int) int { … },`.
	for _, m := range d.Members {
		nameEnd := f.Offset(m.Name.End())
		edits = append(edits, Edit{Start: nameEnd, End: nameEnd, New: ": func"})
		bodyEnd := f.Offset(m.Body.End())
		edits = append(edits, Edit{Start: bodyEnd, End: bodyEnd, New: ","})
	}

	// Tail.
	edits = append(edits, Edit{
		Start: f.Offset(d.Rbrace),
		End:   f.Offset(d.Rbrace) + 1,
		New:   "}\nreturn *" + w + "\n}()",
	})
	if d.TParams != nil {
		// A function, not an IIFE: drop the trailing call.
		edits[len(edits)-1].New = "}\nreturn *" + w + "\n}"
	}
	return edits
}

// instanceClassRef renders the marker's class reference: local classes
// verbatim, imported classes with a quoted package path.
func instanceClassRef(f *syntax.File, class ast.Expr) string {
	root := class
	for {
		switch t := root.(type) {
		case *ast.IndexExpr:
			root = t.X
			continue
		case *ast.IndexListExpr:
			root = t.X
			continue
		}
		break
	}
	sel, isSel := root.(*ast.SelectorExpr)
	if !isSel {
		return string(f.Src[f.Offset(class.Pos()):f.Offset(class.End())])
	}
	alias, _ := sel.X.(*ast.Ident)
	path, ok := importPathFor(f, alias)
	if !ok {
		return string(f.Src[f.Offset(class.Pos()):f.Offset(class.End())])
	}
	// "pkg/path".Name[args]
	tail := string(f.Src[f.Offset(sel.Sel.Pos()):f.Offset(class.End())])
	return strconv.Quote(path) + "." + tail
}
