package resolve

import (
	"fmt"
	"go/types"

	"goforge.dev/gpp/internal/registry"
)

// hit is a resolved generic-method use: the method, the named type instance
// declaring it, and — when reached through embedded fields — the promotion
// path from the receiver expression.
type hit struct {
	method *registry.Method
	named  *types.Named // declaring type, fully instantiated
	path   []string     // embedded field names, outermost first; empty for direct
	// throughPtr: some step of the path goes through a pointer, making the
	// promoted field addressable regardless of the base expression.
	throughPtr bool
	// finalPtr: the last embedded field is itself pointer-typed, so the
	// path expression already denotes a pointer.
	finalPtr bool
	// viaEnum: the receiver is a variant struct and the method belongs to
	// this enum (Some(41).Map(f)); named is the variant instance.
	viaEnum *registry.Enum
}

const maxEmbedDepth = 10

// promote implements Go's promoted-selector rule over the registry: search
// embedded fields breadth-first; the shallowest depth with exactly one
// matching generic method wins; two at the same depth are ambiguous.
// Returns (nil, nil) when no embedded generic method matches.
func promote(reg *registry.Registry, recv types.Type, name string) (*hit, error) {
	type node struct {
		t          types.Type
		path       []string
		throughPtr bool
	}
	base, _ := asNamed(recv)
	if base == nil {
		return nil, nil
	}
	frontier := []node{{t: recv}}
	visited := map[*types.Named]bool{}

	for depth := 0; depth < maxEmbedDepth && len(frontier) > 0; depth++ {
		var next []node
		var found []*hit
		for _, n := range frontier {
			named, wasPtr := asNamed(n.t)
			if named == nil {
				continue
			}

			if depth > 0 && named.Obj().Pkg() != nil {
				if m, ok := reg.Lookup(named.Obj().Pkg().Path(), named.Obj().Name(), name); ok {
					found = append(found, &hit{
						method:     m,
						named:      named,
						path:       n.path,
						throughPtr: n.throughPtr,
						finalPtr:   wasPtr,
					})
					continue
				}
			}

			// visited guards only expansion (pointer-embedding cycles);
			// matching above stays duplicate-visible so same-depth
			// ambiguity is detected like Go's own promotion rule.
			origin := named.Origin()
			if visited[origin] {
				continue
			}
			visited[origin] = true

			st, ok := named.Underlying().(*types.Struct)
			if !ok {
				continue
			}
			for i := 0; i < st.NumFields(); i++ {
				f := st.Field(i)
				if !f.Embedded() {
					continue
				}
				_, fieldIsPtr := asNamed(f.Type())
				path := append(append([]string{}, n.path...), f.Name())
				next = append(next, node{
					t:          f.Type(),
					path:       path,
					throughPtr: n.throughPtr || wasPtr || fieldIsPtr,
				})
			}
		}
		if len(found) == 1 {
			return found[0], nil
		}
		if len(found) > 1 {
			return nil, fmt.Errorf("ambiguous generic method %s: promoted from both %s and %s (select the field explicitly)",
				name, pathString(found[0]), pathString(found[1]))
		}
		frontier = next
	}
	return nil, nil
}

func pathString(h *hit) string {
	out := ""
	for _, p := range h.path {
		out += "." + p
	}
	return out
}
