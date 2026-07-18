package gen

import (
	"go/token"

	"goforge.dev/gpp/internal/diag"
	"goforge.dev/gpp/internal/naming"
)

// planClasses validates class and instance declarations before lowering
// (v0.5.0 pass 1 needs no cross-file class knowledge — witness fields and
// methods render from verbatim source slices; embed flattening, default
// filling, and dictionary wiring happen at resolve).
func planClasses(idx *pkgIndex, tbl *naming.Table) []diag.Diagnostic {
	var diags []diag.Diagnostic
	errAt := func(pos token.Pos, format string, args ...any) {
		diags = append(diags, diag.At(idx.fset.Position(pos), format, args...))
	}

	for _, f := range idx.files {
		if f.gpp == nil {
			continue
		}
		for _, c := range f.gpp.Classes {
			name := c.Spec.Name.Name
			if c.Gen.Lparen.IsValid() || len(c.Gen.Specs) > 1 {
				errAt(c.Spec.Pos(), "declare each class in its own type declaration (class %s is inside a grouped type block)", name)
				continue
			}
			tp := c.Spec.TypeParams
			nTParams := 0
			if tp != nil {
				for _, field := range tp.List {
					nTParams += len(field.Names)
				}
			}
			if nTParams != 1 {
				errAt(c.Spec.Pos(), "a class must have exactly one type parameter (v0.5.0); %s has %d", name, nTParams)
				continue
			}
			if len(c.Members) == 0 {
				errAt(c.ClassPos, "class %s must declare at least one member", name)
				continue
			}
			seenOps := map[string]token.Pos{}
			seenLaws := map[string]token.Pos{}
			for _, m := range c.Members {
				if m.Name == nil {
					continue
				}
				n := m.Name.Name
				if m.LawPos.IsValid() {
					if _, dup := seenLaws[n]; dup {
						errAt(m.Name.Pos(), "class %s declares law %s twice", name, n)
					}
					seenLaws[n] = m.Name.Pos()
				} else {
					if _, dup := seenOps[n]; dup {
						errAt(m.Name.Pos(), "class %s declares operation %s twice", name, n)
					}
					seenOps[n] = m.Name.Pos()
				}
			}
			// Generated method names must not collide with operations.
			for law := range seenLaws {
				if pos, hit := seenOps["Law"+law]; hit {
					errAt(pos, "operation Law%s collides with the generated method for law %s; rename one", law, law)
				}
			}
			for op := range seenOps {
				if pos, hit := seenOps["Default"+op]; hit && "Default"+op != op {
					errAt(pos, "operation Default%s collides with the generated method for %s's default; rename one", op, op)
				}
			}
		}

		for _, d := range f.gpp.Instances {
			// Instance names hide behind BadDecls, so the authored-name
			// sweep misses them; record them here.
			tbl.AddAuthored(d.Name.Name, idx.fset.Position(d.Name.Pos()).String())
			seen := map[string]bool{}
			for _, m := range d.Members {
				if seen[m.Name.Name] {
					errAt(m.Name.Pos(), "instance %s implements %s twice", d.Name.Name, m.Name.Name)
				}
				seen[m.Name.Name] = true
			}
		}
	}
	return diags
}
