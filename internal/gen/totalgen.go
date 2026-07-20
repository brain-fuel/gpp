package gen

import (
	"go/ast"
	"strconv"
	"strings"

	"goforge.dev/goplus/internal/core"
	"goforge.dev/goplus/internal/diag"
	"goforge.dev/goplus/internal/lower"
	"goforge.dev/goplus/internal/registry"
)

// Total functions, pass 1 (v0.7.0). The declaration is validated
// against the v1 surface (every parameter and the single result typed
// `nat`, no receiver), elaborated into the core, and checked locally:
// subtraction obligations under path facts, structural termination
// (import-qualified callees defer existence to resolve). Lowering
// erases nat to int and plants the //goplus:total marker; the erased body
// is the definition importers re-elaborate.

// processTotals validates and lowers one file's total functions.
func processTotals(f *sourceFile, pkgPath string, locals map[string]bool, defs core.Defs) ([]lower.Edit, []*registry.Total, []diag.Diagnostic) {
	var edits []lower.Edit
	var totals []*registry.Total
	var diags []diag.Diagnostic
	errf := func(pos ast.Node, format string, args ...any) {
		diags = append(diags, diag.At(f.gp.Fset.Position(pos.Pos()), format, args...))
	}
	text := func(from, to ast.Node) string {
		return string(f.gp.Src[f.gp.Offset(from.Pos()):f.gp.Offset(to.End())])
	}

	resolve := goplusCallResolver(pkgPath, f.gp.AST)
	for _, t := range f.gp.Totals {
		fd := t.Decl
		if fd.Recv != nil {
			errf(fd, "a total function cannot have a receiver")
			continue
		}
		if fd.Type.TypeParams != nil {
			errf(fd, "a total function cannot have type parameters in v0.7.0")
			continue
		}
		natOK := true
		var natIdents []*ast.Ident
		checkField := func(fl *ast.FieldList, what string) {
			if fl == nil {
				return
			}
			for _, fld := range fl.List {
				id, ok := fld.Type.(*ast.Ident)
				if !ok || id.Name != "nat" {
					errf(fld.Type, "total functions take and return nat in v0.7.0; %s has type %s", what, text(fld.Type, fld.Type))
					natOK = false
					continue
				}
				natIdents = append(natIdents, id)
			}
		}
		checkField(fd.Type.Params, "a parameter")
		if fd.Type.Results == nil || len(fd.Type.Results.List) != 1 {
			errf(fd, "a total function returns exactly one nat")
			natOK = false
		} else {
			checkField(fd.Type.Results, "the result")
		}
		if !natOK {
			continue
		}

		params := paramNamesOf(fd)
		def, err := core.ElabFuncBody(pkgPath+"."+fd.Name.Name, params, fd.Body, resolve)
		if err != nil {
			errf(fd, "%v", err)
			continue
		}
		if err := core.CheckSubtractions(def); err != nil {
			errf(fd, "total function %s: %v", fd.Name.Name, err)
			continue
		}
		callable := func(key string) bool {
			if locals[key] {
				return true
			}
			// Import-qualified callees exist iff their marker is found;
			// that is resolve's audit. Same-package unknowns fail now.
			return !strings.HasPrefix(key, pkgPath+".")
		}
		if err := core.CheckTotal(def, callable); err != nil {
			errf(fd, "%v", err)
			continue
		}
		defs[def.Name] = def

		// Lowering: ONE edit replaces the `total ` keyword (through its
		// trailing whitespace) with the marker line, then nat→int erasure.
		sig := fd.Name.Name + text(fd.Type.Params, fd.Type.Params)
		if fd.Type.Results != nil {
			sig += " " + text(fd.Type.Results, fd.Type.Results)
		}
		start := f.gp.Offset(t.TotalPos)
		end := start + len("total")
		for end < len(f.gp.Src) && (f.gp.Src[end] == ' ' || f.gp.Src[end] == '\t') {
			end++
		}
		edits = append(edits, lower.Edit{Start: start, End: end, New: registry.TotalPrefix + " " + sig + "\n"})
		for _, id := range natIdents {
			edits = append(edits, lower.Edit{
				Start: f.gp.Offset(id.Pos()),
				End:   f.gp.Offset(id.End()),
				New:   "int",
			})
		}
		totals = append(totals, &registry.Total{PkgPath: pkgPath, Name: fd.Name.Name, Sig: sig, Def: def})
	}
	return edits, totals, diags
}

// goplusCallResolver canonicalizes callees in a .gp file (same shape as
// the registry's marker resolver, over the original imports).
func goplusCallResolver(pkgPath string, file *ast.File) core.CallResolver {
	imports := map[string]string{}
	for _, imp := range file.Imports {
		path, err := strconv.Unquote(imp.Path.Value)
		if err != nil {
			continue
		}
		name := path[strings.LastIndex(path, "/")+1:]
		if imp.Name != nil {
			name = imp.Name.Name
		}
		imports[name] = path
	}
	return func(fun ast.Expr) (string, bool) {
		switch fn := fun.(type) {
		case *ast.Ident:
			return pkgPath + "." + fn.Name, true
		case *ast.SelectorExpr:
			alias, ok := fn.X.(*ast.Ident)
			if !ok {
				return "", false
			}
			if path, found := imports[alias.Name]; found {
				return path + "." + fn.Sel.Name, true
			}
		}
		return "", false
	}
}

// paramNamesOf flattens parameter names in order.
func paramNamesOf(fd *ast.FuncDecl) []string {
	var out []string
	if fd.Type.Params == nil {
		return out
	}
	for _, fld := range fd.Type.Params.List {
		for _, n := range fld.Names {
			out = append(out, n.Name)
		}
	}
	return out
}
