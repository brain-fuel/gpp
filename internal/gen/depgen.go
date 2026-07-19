package gen

import (
	"go/ast"
	"strings"

	"goforge.dev/gpp/internal/diag"
	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/registry"
)

// Dependent signatures, pass 1 (v0.7.0). A plain function is DEPENDENT
// when its parameters carry quantities or mention nat. Erasure: nat
// becomes int, 0-quantity parameters are deleted from the signature
// (their call-site arguments drop in resolve), 1/mult quantities strip
// to plain parameters, and the original signature travels in a
// //gpp:dep marker. Total functions keep their own lowering; their
// quantity prefixes (if any) just strip.

// processDeps lowers one file's dependent signatures and quantity
// prefixes.
func processDeps(f *sourceFile, pkgPath string, totals map[*ast.FuncDecl]bool) ([]lower.Edit, []*registry.DepFn, []diag.Diagnostic) {
	var edits []lower.Edit
	var deps []*registry.DepFn
	var diags []diag.Diagnostic
	src := f.gpp
	errf := func(pos ast.Node, format string, args ...any) {
		diags = append(diags, diag.At(src.Fset.Position(pos.Pos()), format, args...))
	}
	text := func(from, to ast.Node) string {
		return string(src.Src[src.Offset(from.Pos()):src.Offset(to.End())])
	}

	// Quantity lookup by parameter-name identity.
	qByName := map[*ast.Ident]string{}
	for _, q := range f.gpp.Quantities {
		qByName[q.Name] = q.Quantity
	}
	qEditByName := map[*ast.Ident]bool{}

	for _, decl := range f.gpp.AST.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Type.Params == nil {
			continue
		}
		if totals[fd] {
			continue // total lowering owns these
		}
		var natIdents []*ast.Ident
		collectNat := func(fl *ast.FieldList) {
			if fl == nil {
				return
			}
			for _, fld := range fl.List {
				ast.Inspect(fld.Type, func(n ast.Node) bool {
					if id, ok := n.(*ast.Ident); ok && id.Name == "nat" {
						natIdents = append(natIdents, id)
					}
					return true
				})
			}
		}
		collectNat(fd.Type.Params)
		collectNat(fd.Type.Results)

		type param struct {
			field    *ast.Field
			name     *ast.Ident
			quantity string
			typeText string
		}
		var params []param
		hasQuantity := false
		for _, fld := range fd.Type.Params.List {
			tt := text(fld.Type, fld.Type)
			for _, n := range fld.Names {
				q := qByName[n]
				if q != "" {
					hasQuantity = true
				}
				params = append(params, param{field: fld, name: n, quantity: q, typeText: tt})
			}
		}
		if !hasQuantity && len(natIdents) == 0 {
			continue
		}
		if fd.Recv != nil {
			errf(fd, "a dependent signature cannot have a receiver in v0.7.0")
			continue
		}

		// Marker: flattened original signature with quantities.
		var parts []string
		for _, p := range params {
			seg := p.name.Name + " " + p.typeText
			if p.quantity != "" {
				seg = p.quantity + " " + seg
			}
			parts = append(parts, seg)
		}
		sig := fd.Name.Name
		if fd.Type.TypeParams != nil {
			sig += "[" + string(src.Src[src.Offset(fd.Type.TypeParams.Opening)+1:src.Offset(fd.Type.TypeParams.Closing)]) + "]"
		}
		sig += "(" + strings.Join(parts, ", ") + ")"
		if fd.Type.Results != nil {
			sig += " " + text(fd.Type.Results, fd.Type.Results)
		}
		d, derr := registry.ParseDepSig(pkgPath, sig)
		if derr != nil {
			errf(fd, "%v", derr)
			continue
		}
		deps = append(deps, d)
		at := src.Offset(fd.Pos())
		for at > 0 && src.Src[at-1] != '\n' {
			at--
		}
		edits = append(edits, lower.Edit{Start: at, End: at, New: registry.DepPrefix + " " + sig + "\n"})

		// 0-params: delete the whole parameter (with its comma). Other
		// quantities strip via the shared quantity edit below.
		droppedFields := map[*ast.Field]bool{}
		for i, p := range params {
			if p.quantity != "0" {
				continue
			}
			if len(p.field.Names) > 1 {
				errf(p.name, "declare an erased parameter in its own declaration (not a shared-type group)")
				continue
			}
			qEditByName[p.name] = true // suppress the plain strip
			droppedFields[p.field] = true
			start := src.Offset(p.field.Pos())
			// The quantity literal precedes the field start.
			for _, q := range f.gpp.Quantities {
				if q.Name == p.name {
					start = src.Offset(q.QPos)
				}
			}
			end := src.Offset(p.field.End())
			if i+1 < len(params) {
				end = src.Offset(params[i+1].field.Pos())
				for _, q := range f.gpp.Quantities {
					if q.Name == params[i+1].name && src.Offset(q.QPos) < end {
						end = src.Offset(q.QPos)
					}
				}
			} else if i > 0 {
				start = src.Offset(params[i-1].field.End())
			}
			edits = append(edits, lower.Edit{Start: start, End: end, New: ""})
		}
		for _, id := range natIdents {
			inDropped := false
			for fld := range droppedFields {
				if id.Pos() >= fld.Pos() && id.End() <= fld.End() {
					inDropped = true
				}
			}
			if inDropped {
				continue // the whole parameter is deleted
			}
			edits = append(edits, lower.Edit{Start: src.Offset(id.Pos()), End: src.Offset(id.End()), New: "int"})
		}
	}

	// Quantity prefixes not consumed by 0-param deletion strip plainly
	// (1/mult everywhere, and 0 inside func literals or totals).
	for _, q := range f.gpp.Quantities {
		if qEditByName[q.Name] {
			continue
		}
		edits = append(edits, lower.QuantityEdits(f.gpp, q)...)
	}
	return edits, deps, diags
}
