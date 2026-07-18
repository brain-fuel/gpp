package lower

import (
	"fmt"
	"go/ast"
	"go/token"
	"regexp"
	"strconv"
	"strings"

	"goforge.dev/gpp/internal/directive"
	"goforge.dev/gpp/internal/syntax"
)

// Class lowering (v0.5.0). A class becomes a witness struct whose fields
// are the operations; laws and defaults become methods spliced AROUND
// their bodies, so body bytes stay in place (tight sourcemap, and nested
// G++ constructs inside bodies lower independently):
//
//	type Monoid[T any] class {        //gpp:class Monoid[T any] embeds(Semigroup)
//		Semigroup[T]                  type Monoid[T any] struct {
//		Empty() T                 ⇒       Semigroup[T]        // flattened in pass 2
//		law LeftId(a T) { … }             Empty func() T
//	}                                 }
//	                                  //gpp:law (Monoid[T]) LeftId(a T)
//	                                  func (m Monoid[T]) LawLeftId(a T) bool { … }

// ClassEdits lowers one class declaration.
func ClassEdits(f *syntax.File, c *syntax.ClassDecl) []Edit {
	name := c.Spec.Name.Name
	tparamsSrc := ""
	tparamName := ""
	if c.Spec.TypeParams != nil {
		tparamsSrc = string(f.Src[f.Offset(c.Spec.TypeParams.Opening)+1 : f.Offset(c.Spec.TypeParams.Closing)])
		if len(c.Spec.TypeParams.List) > 0 && len(c.Spec.TypeParams.List[0].Names) > 0 {
			tparamName = c.Spec.TypeParams.List[0].Names[0].Name
		}
	}
	recvType := name + bracket(tparamName)
	recv := freshName(f, c.Spec.Pos(), c.Rbrace, "m")

	var edits []Edit

	// Marker above the declaration (above its doc comment).
	marker := directive.ClassMarker{Name: name, TParams: tparamsSrc, Embeds: classEmbedRefs(f, c)}
	at := lineStartBefore(f, c.Gen)
	edits = append(edits, Edit{Start: at, End: at, New: marker.String() + "\n"})

	// Header: `class {` → the complete witness struct (fields synthesized
	// from verbatim member slices), followed by nothing — member spans are
	// deleted or become methods in place.
	var fields []string
	for _, m := range c.Members {
		switch {
		case m.Embed != nil:
			fields = append(fields, string(f.Src[f.Offset(m.Embed.Pos()):f.Offset(m.Embed.End())]))
		case m.Body == nil && m.Name != nil:
			// Bodiless op: `Empty() T` → field `Empty func() T`.
			end := m.Params.End()
			if m.Result != nil {
				end = m.Result.End()
			}
			fields = append(fields, m.Name.Name+" func"+string(f.Src[f.Offset(m.Params.Pos()):f.Offset(end)]))
		case m.Body != nil && !m.LawPos.IsValid():
			// Default op: it is ALSO a field (instances may override it).
			end := m.Params.End()
			if m.Result != nil {
				end = m.Result.End()
			}
			fields = append(fields, m.Name.Name+" func"+string(f.Src[f.Offset(m.Params.Pos()):f.Offset(end)]))
		}
	}
	var b strings.Builder
	b.WriteString("struct {\n")
	for _, fd := range fields {
		b.WriteString("\t" + fd + "\n")
	}
	b.WriteString("}")
	edits = append(edits, Edit{Start: f.Offset(c.ClassPos), End: f.Offset(c.Lbrace) + 1, New: b.String()})

	// Members.
	for _, m := range c.Members {
		switch {
		case m.Embed != nil:
			edits = append(edits, Edit{Start: f.Offset(m.Embed.Pos()), End: f.Offset(m.Embed.End()), New: ""})
		case m.Body == nil && m.Name != nil:
			end := m.Params.End()
			if m.Result != nil {
				end = m.Result.End()
			}
			edits = append(edits, Edit{Start: f.Offset(m.Name.Pos()), End: f.Offset(end), New: ""})
		case m.LawPos.IsValid():
			paramsText := string(f.Src[f.Offset(m.Params.Opening)+1 : f.Offset(m.Params.Closing)])
			lm := directive.LawMarker{ClassName: name, ClassTParam: tparamName, Name: m.Name.Name, Params: paramsText}
			at := lineStartBeforeMember(f, m)
			edits = append(edits, Edit{Start: at, End: at, New: lm.String() + "\n"})
			edits = append(edits, Edit{
				Start: f.Offset(m.LawPos),
				End:   f.Offset(m.Name.End()),
				New:   fmt.Sprintf("func (%s %s) Law%s", recv, recvType, m.Name.Name),
			})
			// Implicit bool result before the body.
			after := f.Offset(m.Params.Closing) + 1
			edits = append(edits, Edit{Start: after, End: after, New: " bool"})
		default:
			// Default op → method.
			paramsText := string(f.Src[f.Offset(m.Params.Opening)+1 : f.Offset(m.Params.Closing)])
			dm := directive.LawMarker{ClassName: name, ClassTParam: tparamName, Name: m.Name.Name, Params: paramsText}
			at := lineStartBeforeMember(f, m)
			edits = append(edits, Edit{Start: at, End: at, New: directive.DefaultMarkerString(dm) + "\n"})
			edits = append(edits, Edit{
				Start: f.Offset(m.Name.Pos()),
				End:   f.Offset(m.Name.End()),
				New:   fmt.Sprintf("func (%s %s) Default%s", recv, recvType, m.Name.Name),
			})
		}
	}

	// The class's closing brace is consumed by the struct header.
	edits = append(edits, Edit{Start: f.Offset(c.Rbrace), End: f.Offset(c.Rbrace) + 1, New: ""})
	return edits
}

// classEmbedRefs renders the marker's embeds clause entries: local classes
// bare, imported classes as "pkg/path".Name.
func classEmbedRefs(f *syntax.File, c *syntax.ClassDecl) []string {
	var out []string
	for _, m := range c.Members {
		if m.Embed == nil {
			continue
		}
		root := m.Embed
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
		switch t := root.(type) {
		case *ast.Ident:
			out = append(out, t.Name)
		case *ast.SelectorExpr:
			alias, _ := t.X.(*ast.Ident)
			if path, ok := importPathFor(f, alias); ok {
				out = append(out, strconv.Quote(path)+"."+t.Sel.Name)
			} else {
				out = append(out, t.Sel.Name)
			}
		}
	}
	return out
}

// importPathFor resolves a file-local import alias to its package path.
func importPathFor(f *syntax.File, alias *ast.Ident) (string, bool) {
	if alias == nil {
		return "", false
	}
	for _, imp := range f.AST.Imports {
		path, err := strconv.Unquote(imp.Path.Value)
		if err != nil {
			continue
		}
		name := ""
		if imp.Name != nil {
			name = imp.Name.Name
		} else {
			if i := strings.LastIndex(path, "/"); i >= 0 {
				name = path[i+1:]
			} else {
				name = path
			}
		}
		if name == alias.Name {
			return path, true
		}
	}
	return "", false
}

// lineStartBefore finds the line-start insertion offset above a decl's doc.
func lineStartBefore(f *syntax.File, gd *ast.GenDecl) int {
	at := f.Offset(gd.Pos())
	if gd != nil && gd.Doc != nil {
		at = f.Offset(gd.Doc.Pos())
	}
	for at > 0 && f.Src[at-1] != '\n' {
		at--
	}
	return at
}

// lineStartBeforeMember finds the line-start offset above a class member
// (above its doc comment when present).
func lineStartBeforeMember(f *syntax.File, m *syntax.ClassMember) int {
	pos := m.Name.Pos()
	if m.LawPos.IsValid() {
		pos = m.LawPos
	}
	at := f.Offset(pos)
	if m.Doc != nil {
		at = f.Offset(m.Doc.Pos())
	}
	for at > 0 && f.Src[at-1] != '\n' {
		at--
	}
	return at
}

// freshName picks an identifier not occurring anywhere in [from, to) —
// receivers and constructor temps must not capture user names.
func freshName(f *syntax.File, from, to token.Pos, base string) string {
	span := f.Src[f.Offset(from):f.Offset(to)]
	used := map[string]bool{}
	for _, m := range identRe.FindAll(span, -1) {
		used[string(m)] = true
	}
	if !used[base] {
		return base
	}
	for i := 1; ; i++ {
		cand := fmt.Sprintf("%s%d", base, i)
		if !used[cand] {
			return cand
		}
	}
}

var identRe = regexp.MustCompile(`[A-Za-z_][A-Za-z0-9_]*`)
