// Package directive parses and renders goplus directive comments:
//
//	//goplus:method (Stack[T]) Map[U] — marker above a lowered function
package directive

import (
	"fmt"
	"strings"
)

const (
	methodPrefix = "//goplus:method"
)

// Marker is the machine-readable description of a lowered generic method,
// rendered as a comment directly above the generated function.
type Marker struct {
	Pointer       bool   // pointer receiver
	RecvType      string // base receiver type name, e.g. "Stack"
	RecvTParams   string // receiver type parameter names as written, e.g. "T" or "K, V"; "" if none
	Method        string // original method name, e.g. "Map"
	MethodTParams string // method type parameter names, e.g. "U"
	FuncName      string // generated function name, e.g. "StackMap"
}

// String renders the marker comment line (without trailing newline).
func (m Marker) String() string {
	var b strings.Builder
	b.WriteString(methodPrefix)
	b.WriteString(" (")
	if m.Pointer {
		b.WriteByte('*')
	}
	b.WriteString(m.RecvType)
	if m.RecvTParams != "" {
		fmt.Fprintf(&b, "[%s]", m.RecvTParams)
	}
	b.WriteString(") ")
	b.WriteString(m.Method)
	if m.MethodTParams != "" {
		fmt.Fprintf(&b, "[%s]", m.MethodTParams)
	}
	return b.String()
}

// ParseMarker parses a comment line of the form rendered by Marker.String.
// The FuncName field is not part of the comment; callers pair the marker with
// the function declaration it precedes.
func ParseMarker(line string) (Marker, bool) {
	rest, ok := strings.CutPrefix(strings.TrimSpace(line), methodPrefix)
	if !ok || rest == "" || (rest[0] != ' ' && rest[0] != '\t') {
		return Marker{}, false
	}
	rest = strings.TrimSpace(rest)
	if !strings.HasPrefix(rest, "(") {
		return Marker{}, false
	}
	close := strings.Index(rest, ")")
	if close < 0 {
		return Marker{}, false
	}
	recv := strings.TrimSpace(rest[1:close])
	method := strings.TrimSpace(rest[close+1:])
	var m Marker
	if strings.HasPrefix(recv, "*") {
		m.Pointer = true
		recv = strings.TrimSpace(recv[1:])
	}
	m.RecvType, m.RecvTParams, ok = splitNameTParams(recv)
	if !ok || m.RecvType == "" {
		return Marker{}, false
	}
	m.Method, m.MethodTParams, ok = splitNameTParams(method)
	if !ok || m.Method == "" {
		return Marker{}, false
	}
	return m, true
}

// splitNameTParams splits "Stack[T, U]" into ("Stack", "T, U").
func splitNameTParams(s string) (name, tparams string, ok bool) {
	open := strings.Index(s, "[")
	if open < 0 {
		return s, "", true
	}
	if !strings.HasSuffix(s, "]") {
		return "", "", false
	}
	return s[:open], strings.TrimSpace(s[open+1 : len(s)-1]), true
}
