package directive

import (
	"fmt"
	"strings"
)

const (
	classPrefix    = "//goplus:class"
	lawPrefix      = "//goplus:law"
	defaultPrefix  = "//goplus:default"
	instancePrefix = "//goplus:instance"
	fnPrefix       = "//goplus:fn"
)

// ClassMarker is rendered above the generated witness struct:
//
//	//goplus:class Monoid[T any] embeds(Semigroup, "example.com/x".Eq)
//
// Embeds name sibling classes bare and imported classes as a quoted
// package path plus .Name. Unknown trailing clauses are ignored by the
// parser (reserved for later milestones, e.g. derive(…)).
type ClassMarker struct {
	Name    string   // class name, e.g. "Monoid"
	TParams string   // type parameter list with constraint, e.g. "T any"
	Embeds  []string // each "Semigroup" or `"pkg/path".Name`
}

func (m ClassMarker) String() string {
	var b strings.Builder
	fmt.Fprintf(&b, "%s %s[%s]", classPrefix, m.Name, m.TParams)
	if len(m.Embeds) > 0 {
		fmt.Fprintf(&b, " embeds(%s)", strings.Join(m.Embeds, ", "))
	}
	return b.String()
}

// ParseClassMarker parses a comment line rendered by ClassMarker.String.
func ParseClassMarker(line string) (ClassMarker, bool) {
	rest, ok := cutDirective(line, classPrefix)
	if !ok {
		return ClassMarker{}, false
	}
	var m ClassMarker
	m.Name, m.TParams, ok = splitNameTParams(firstField(rest))
	if !ok || m.Name == "" {
		return ClassMarker{}, false
	}
	rest = strings.TrimSpace(rest[len(firstField(rest)):])
	if clause, found := strings.CutPrefix(rest, "embeds("); found {
		close := strings.Index(clause, ")")
		if close < 0 {
			return ClassMarker{}, false
		}
		for _, e := range strings.Split(clause[:close], ",") {
			if t := strings.TrimSpace(e); t != "" {
				m.Embeds = append(m.Embeds, t)
			}
		}
	}
	return m, true
}

// LawMarker is rendered above each generated law method:
//
//	//goplus:law (Semigroup[T]) Assoc(a, b, c T)
type LawMarker struct {
	ClassName   string
	ClassTParam string // tparam name only, e.g. "T"
	Name        string
	Params      string // verbatim
}

func (m LawMarker) String() string {
	return fmt.Sprintf("%s (%s[%s]) %s(%s)", lawPrefix, m.ClassName, m.ClassTParam, m.Name, m.Params)
}

// ParseLawMarker parses a comment line rendered by LawMarker.String.
func ParseLawMarker(line string) (LawMarker, bool) {
	return parseRecvMember(line, lawPrefix)
}

// DefaultMarker is rendered above each generated default-op method:
//
//	//goplus:default (Group[T]) LeftDiv(a, b T)
type DefaultMarker = LawMarker

// ParseDefaultMarker parses a comment line rendered for a default op.
func ParseDefaultMarker(line string) (LawMarker, bool) {
	return parseRecvMember(line, defaultPrefix)
}

// DefaultMarkerString renders a default-op marker.
func DefaultMarkerString(m LawMarker) string {
	return fmt.Sprintf("%s (%s[%s]) %s(%s)", defaultPrefix, m.ClassName, m.ClassTParam, m.Name, m.Params)
}

func parseRecvMember(line, prefix string) (LawMarker, bool) {
	rest, ok := cutDirective(line, prefix)
	if !ok || !strings.HasPrefix(rest, "(") {
		return LawMarker{}, false
	}
	close := strings.Index(rest, ")")
	if close < 0 {
		return LawMarker{}, false
	}
	var m LawMarker
	m.ClassName, m.ClassTParam, ok = splitNameTParams(strings.TrimSpace(rest[1:close]))
	if !ok || m.ClassName == "" {
		return LawMarker{}, false
	}
	rest = strings.TrimSpace(rest[close+1:])
	open := strings.Index(rest, "(")
	if open < 0 {
		// Name only (params omitted).
		m.Name = strings.TrimSpace(rest)
		return m, m.Name != ""
	}
	m.Name = strings.TrimSpace(rest[:open])
	depth := 0
	for i, r := range rest[open:] {
		if r == '(' {
			depth++
		}
		if r == ')' {
			depth--
			if depth == 0 {
				m.Params = strings.TrimSpace(rest[open+1 : open+i])
				return m, m.Name != ""
			}
		}
	}
	return LawMarker{}, false
}

// InstanceMarker is rendered above each generated instance value:
//
//	//goplus:instance IntAdd Group[int]
//	//goplus:instance SliceConcat[T any] Monoid[[]T]
//	//goplus:instance Lex "goforge.dev/goplus/std/algebra".Monoid[string]
type InstanceMarker struct {
	Name    string
	TParams string // generic instances; "" otherwise
	Class   string // class ref verbatim: Name[args] or "pkg/path".Name[args]
}

func (m InstanceMarker) String() string {
	var b strings.Builder
	b.WriteString(instancePrefix + " " + m.Name)
	if m.TParams != "" {
		fmt.Fprintf(&b, "[%s]", m.TParams)
	}
	b.WriteString(" " + m.Class)
	return b.String()
}

// ParseInstanceMarker parses a comment line rendered by InstanceMarker.String.
func ParseInstanceMarker(line string) (InstanceMarker, bool) {
	rest, ok := cutDirective(line, instancePrefix)
	if !ok {
		return InstanceMarker{}, false
	}
	head := firstField(rest)
	var m InstanceMarker
	m.Name, m.TParams, ok = splitNameTParams(head)
	if !ok || m.Name == "" {
		return InstanceMarker{}, false
	}
	m.Class = strings.TrimSpace(rest[len(head):])
	return m, m.Class != ""
}

// FnMarker is rendered above each dictionary-taking generated function:
//
//	//goplus:fn Accumulate[T Monoid]
//	//goplus:fn Lex[T "goforge.dev/goplus/std/algebra".Monoid]
//
// The bracket list holds one `tparam class` pair per dictionary parameter,
// in dictionary order, comma-separated.
type FnMarker struct {
	Name        string
	Constraints string // verbatim bracket contents
}

func (m FnMarker) String() string {
	return fmt.Sprintf("%s %s[%s]", fnPrefix, m.Name, m.Constraints)
}

// ParseFnMarker parses a comment line rendered by FnMarker.String.
func ParseFnMarker(line string) (FnMarker, bool) {
	rest, ok := cutDirective(line, fnPrefix)
	if !ok {
		return FnMarker{}, false
	}
	var m FnMarker
	m.Name, m.Constraints, ok = splitNameTParams(rest)
	if !ok || m.Name == "" || m.Constraints == "" {
		return FnMarker{}, false
	}
	return m, true
}

// firstField returns the leading whitespace-delimited field of s, keeping
// bracketed sections intact ("SliceConcat[T any]" is one field).
func firstField(s string) string {
	depth := 0
	for i, r := range s {
		switch r {
		case '[', '(':
			depth++
		case ']', ')':
			depth--
		case ' ', '\t':
			if depth == 0 {
				return s[:i]
			}
		}
	}
	return s
}
