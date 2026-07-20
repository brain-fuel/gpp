package resolve

import (
	"go/ast"
	"strings"

	"goforge.dev/goplus/internal/core"
	"goforge.dev/goplus/internal/registry"
)

// Total functions, resolve side (v0.7.0). Pass 1 elaborated and checked
// each local total against local knowledge; import-qualified callees
// deferred existence to here, where the registry has every reachable
// package's //goplus:total markers. Pure audit: nothing rewrites.

// totalCandidate audits one marked total function's cross-package calls.
func (r *fileResolver) totalCandidate(fd *ast.FuncDecl) {
	if !r.report || fd.Doc == nil {
		return
	}
	marked := false
	for _, c := range fd.Doc.List {
		if strings.HasPrefix(c.Text, registry.TotalPrefix+" ") {
			marked = true
		}
	}
	if !marked {
		return
	}
	tot, ok := r.reg.LookupTotal(r.pkg.PkgPath, fd.Name.Name)
	if !ok || tot.Def == nil {
		return
	}
	walkCalls(tot.Def.Body, func(key string) {
		if key == tot.Def.Name {
			return
		}
		if _, found := r.reg.LookupTotal(splitKey(key)); !found {
			r.errorf(fd.Pos(), "total function %s calls %s, which is not a total function (no //goplus:total marker found)",
				fd.Name.Name, key)
		}
	})
}

func walkCalls(t core.Term, visit func(key string)) {
	switch x := t.(type) {
	case core.Prim:
		for _, a := range x.Args {
			walkCalls(a, visit)
		}
	case core.Ctor:
		for _, a := range x.Args {
			walkCalls(a, visit)
		}
	case core.Call:
		visit(x.Fn)
		for _, a := range x.Args {
			walkCalls(a, visit)
		}
	case core.If:
		walkCalls(x.L, visit)
		walkCalls(x.R, visit)
		walkCalls(x.Then, visit)
		walkCalls(x.Else, visit)
	case core.MatchT:
		walkCalls(x.Scrut, visit)
		for _, arm := range x.Arms {
			walkCalls(arm.Body, visit)
		}
	}
}

// splitKey divides a canonical "pkgpath.Name" definition key.
func splitKey(key string) (pkgPath, name string) {
	i := strings.LastIndex(key, ".")
	if i < 0 {
		return "", key
	}
	return key[:i], key[i+1:]
}
