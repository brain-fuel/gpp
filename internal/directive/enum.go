package directive

import (
	"fmt"
	"strings"
)

const (
	enumPrefix    = "//gpp:enum"
	variantPrefix = "//gpp:variant"
)

// EnumMarker is the machine-readable description of a lowered enum,
// rendered above the generated sealed interface:
//
//	//gpp:enum Option[T any]
type EnumMarker struct {
	Name    string // enum type name, e.g. "Option"
	TParams string // type parameter list with constraints, e.g. "T any"; "" if none
}

func (m EnumMarker) String() string {
	if m.TParams == "" {
		return enumPrefix + " " + m.Name
	}
	return fmt.Sprintf("%s %s[%s]", enumPrefix, m.Name, m.TParams)
}

// ParseEnumMarker parses a comment line rendered by EnumMarker.String.
func ParseEnumMarker(line string) (EnumMarker, bool) {
	rest, ok := cutDirective(line, enumPrefix)
	if !ok {
		return EnumMarker{}, false
	}
	name, tparams, ok := splitNameTParams(rest)
	if !ok || name == "" {
		return EnumMarker{}, false
	}
	return EnumMarker{Name: name, TParams: tparams}, true
}

// VariantMarker is rendered above each generated variant struct:
//
//	//gpp:variant (Option[T]) Some(value T)
//	//gpp:variant (Expr[T]) Lit(v int) Expr[int]
type VariantMarker struct {
	EnumName    string // "Option"
	EnumTParams string // tparam names only, e.g. "T"; "" if none
	Name        string // variant name as written in G++, e.g. "Some"
	Params      string // constructor params verbatim, e.g. "value T"; "" if nullary
	HasParams   bool   // distinguishes None from None()
	Result      string // GADT result type verbatim, e.g. "Expr[int]"; "" if defaulted
}

func (m VariantMarker) String() string {
	var b strings.Builder
	b.WriteString(variantPrefix)
	b.WriteString(" (")
	b.WriteString(m.EnumName)
	if m.EnumTParams != "" {
		fmt.Fprintf(&b, "[%s]", m.EnumTParams)
	}
	b.WriteString(") ")
	b.WriteString(m.Name)
	if m.HasParams {
		fmt.Fprintf(&b, "(%s)", m.Params)
	}
	if m.Result != "" {
		b.WriteString(" " + m.Result)
	}
	return b.String()
}

// ParseVariantMarker parses a comment line rendered by VariantMarker.String.
func ParseVariantMarker(line string) (VariantMarker, bool) {
	rest, ok := cutDirective(line, variantPrefix)
	if !ok {
		return VariantMarker{}, false
	}
	if !strings.HasPrefix(rest, "(") {
		return VariantMarker{}, false
	}
	close := strings.Index(rest, ")")
	if close < 0 {
		return VariantMarker{}, false
	}
	var m VariantMarker
	m.EnumName, m.EnumTParams, ok = splitNameTParams(strings.TrimSpace(rest[1:close]))
	if !ok || m.EnumName == "" {
		return VariantMarker{}, false
	}
	rest = strings.TrimSpace(rest[close+1:])

	// Variant name up to '(' or whitespace.
	end := len(rest)
	if i := strings.IndexAny(rest, "( \t"); i >= 0 {
		end = i
	}
	m.Name = rest[:end]
	if m.Name == "" {
		return VariantMarker{}, false
	}
	rest = rest[end:]
	if strings.HasPrefix(rest, "(") {
		// Params run to the matching close paren (params may nest parens
		// in func types).
		depth := 0
		for i, r := range rest {
			if r == '(' {
				depth++
			}
			if r == ')' {
				depth--
				if depth == 0 {
					m.HasParams = true
					m.Params = strings.TrimSpace(rest[1:i])
					rest = rest[i+1:]
					break
				}
			}
		}
		if !m.HasParams {
			return VariantMarker{}, false
		}
	}
	m.Result = strings.TrimSpace(rest)
	return m, true
}

// cutDirective strips a directive prefix followed by whitespace.
func cutDirective(line, prefix string) (string, bool) {
	rest, ok := strings.CutPrefix(strings.TrimSpace(line), prefix)
	if !ok || rest == "" || (rest[0] != ' ' && rest[0] != '\t') {
		return "", false
	}
	return strings.TrimSpace(rest), true
}
