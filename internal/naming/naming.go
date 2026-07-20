// Package naming implements the lowered-name scheme: a lowered function
// keeps its method's own name when that name is unique in the package,
// falling back to the receiver-prefixed concatenation when it collides —
// the same discipline enum variant structs use. Visibility never widens:
// the name is exported iff BOTH the receiver type and the member are.
package naming

import (
	"fmt"
	"go/ast"
	"go/token"
	"unicode"
	"unicode/utf8"
)

// BareName is the preferred lowered name: the member's own name, cased so
// the result is exported iff BOTH owner and member are exported.
//
//	(Stack).Map -> Map    (stack).Map -> map    (Stack).map -> map
func BareName(owner, member string) string {
	return setFirstCase(member, ast.IsExported(owner) && ast.IsExported(member))
}

// PrefixedName is the collision fallback: concat(owner, Capitalize(member)),
// exported iff both are.
//
//	(Stack).Map -> StackMap    (stack).Map -> stackMap
func PrefixedName(owner, member string) string {
	exported := ast.IsExported(owner) && ast.IsExported(member)
	return setFirstCase(owner, exported) + capitalize(member)
}

// FuncName picks the lowered function name for a method: the bare method
// name when it is viable (not a keyword) and unshared in the package,
// the prefixed form otherwise. shared counts bare candidates across the
// package's lowered methods.
func FuncName(recvType, method string, shared map[string]int) string {
	bare := BareName(recvType, method)
	if !token.IsKeyword(bare) && shared[bare] <= 1 {
		return bare
	}
	return PrefixedName(recvType, method)
}

func capitalize(s string) string { return setFirstCase(s, true) }

func setFirstCase(s string, upper bool) string {
	r, size := utf8.DecodeRuneInString(s)
	if r == utf8.RuneError {
		return s
	}
	mapped := unicode.ToLower(r)
	if upper {
		mapped = unicode.ToUpper(r)
	}
	if mapped == r {
		return s
	}
	return string(mapped) + s[size:]
}

// Table detects name collisions between generated functions and any other
// package-scope declaration (authored or generated).
type Table struct {
	entries map[string]entry
}

type entry struct {
	origin    string
	generated bool
}

func NewTable() *Table { return &Table{entries: map[string]entry{}} }

// AddAuthored records an existing package-scope identifier, e.g.
// AddAuthored("StackMap", "util.go:14:1"). Authored identifiers never
// collide with each other (go/types owns that); they only reserve names.
func (t *Table) AddAuthored(name, origin string) {
	if _, exists := t.entries[name]; !exists {
		t.entries[name] = entry{origin: origin}
	}
}

// Has reports whether a name is already reserved (authored or generated).
func (t *Table) Has(name string) bool {
	_, exists := t.entries[name]
	return exists
}

// AddGenerated records a generated function name, returning an error if the
// name is already taken by an authored declaration or another generated
// function. origin describes the method, e.g. `method (Stack[T]) Map[U] at
// stack.gp:5:1`.
func (t *Table) AddGenerated(name, origin string) error {
	if prev, exists := t.entries[name]; exists {
		kind := "declaration"
		if prev.generated {
			kind = "generated function"
		}
		return fmt.Errorf("generated name %s for %s collides with %s at %s; rename the method or the conflicting declaration",
			name, origin, kind, prev.origin)
	}
	t.entries[name] = entry{origin: origin, generated: true}
	return nil
}
