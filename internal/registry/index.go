package registry

import (
	"strings"
)

// Indexed enums (v0.7.0). An enum type parameter whose constraint is
// `nat` (later: a first-order data type) is a VALUE INDEX binder: it
// exists only at check time. Erasure drops index binders from the
// enum's Go type parameters and index arguments from every
// instantiation — the generated world never sees them; the index model
// travels through the unerased marker texts.

// IndexBinder is one value-index binder of an indexed enum.
type IndexBinder struct {
	Name string // binder name, e.g. "n"
	Sort string // "nat" (v0.7.0 4a)
	Pos  int    // position in the original type-parameter list
}

// SplitBinders partitions a tparam list text ("T any, n nat") into
// erased type-parameter names and index binders.
func SplitBinders(tparams string) (typeNames []string, indices []IndexBinder) {
	for i, p := range parseParamList(tparams) {
		if p.Type == "nat" {
			indices = append(indices, IndexBinder{Name: p.Name, Sort: p.Type, Pos: i})
		} else {
			typeNames = append(typeNames, p.Name)
		}
	}
	return typeNames, indices
}

// IndexArity answers, for a type name, which of its argument positions
// are indices, and its total arity.
type IndexArity func(name string) (idxPos map[int]bool, arity int, ok bool)

// EraseIndexArgs removes index arguments from every instantiation of a
// known indexed type inside a type text: `Vec[T, n+1]` becomes
// `Vec[T]`, and an instantiation left with no arguments loses its
// brackets. The scan is textual — index arguments are TERMS, which
// go/parser refuses in type-argument position.
func EraseIndexArgs(text string, isIndexed IndexArity) (string, error) {
	erased, _, err := EraseCollectIndexArgs(text, isIndexed)
	return erased, err
}

// EraseCollectIndexArgs is EraseIndexArgs returning also the dropped
// index-argument texts (outermost-first) for validation.
func EraseCollectIndexArgs(text string, isIndexed IndexArity) (string, []string, error) {
	if !strings.Contains(text, "[") {
		return text, nil, nil
	}
	var dropped []string
	var out strings.Builder
	i := 0
	for i < len(text) {
		c := text[i]
		if isIdentByte(c, true) {
			j := i + 1
			for j < len(text) && isIdentByte(text[j], false) {
				j++
			}
			name := text[i:j]
			if j < len(text) && text[j] == '[' {
				close := matchBracket(text, j)
				if close < 0 {
					out.WriteString(text[i:])
					return out.String(), dropped, nil
				}
				inner := text[j+1 : close]
				args := splitTopLevel(inner, ',')
				idxPos, arity, indexed := isIndexed(name)
				if indexed && len(args) == arity {
					var kept []string
					for ai, a := range args {
						if idxPos[ai] {
							dropped = append(dropped, strings.TrimSpace(a))
							continue
						}
						ka, kd, err := EraseCollectIndexArgs(strings.TrimSpace(a), isIndexed)
						if err != nil {
							return "", nil, err
						}
						dropped = append(dropped, kd...)
						kept = append(kept, ka)
					}
					out.WriteString(name)
					if len(kept) > 0 {
						out.WriteString("[" + strings.Join(kept, ", ") + "]")
					}
				} else {
					ei, ed, err := EraseCollectIndexArgs(inner, isIndexed)
					if err != nil {
						return "", nil, err
					}
					dropped = append(dropped, ed...)
					out.WriteString(name + "[" + ei + "]")
				}
				i = close + 1
				continue
			}
			out.WriteString(name)
			i = j
			continue
		}
		if c == '[' {
			// A non-instantiation bracket (array/slice/map index side):
			// recurse into its contents.
			close := matchBracket(text, i)
			if close < 0 {
				out.WriteString(text[i:])
				return out.String(), dropped, nil
			}
			ei, ed, err := EraseCollectIndexArgs(text[i+1:close], isIndexed)
			if err != nil {
				return "", nil, err
			}
			dropped = append(dropped, ed...)
			out.WriteString("[" + ei + "]")
			i = close + 1
			continue
		}
		out.WriteByte(c)
		i++
	}
	return out.String(), dropped, nil
}

// matchBracket finds the ] matching the [ at position open.
func matchBracket(s string, open int) int {
	depth := 0
	for i := open; i < len(s); i++ {
		switch s[i] {
		case '[':
			depth++
		case ']':
			depth--
			if depth == 0 {
				return i
			}
		}
	}
	return -1
}

func isIdentByte(c byte, start bool) bool {
	if c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') {
		return true
	}
	return !start && c >= '0' && c <= '9'
}
