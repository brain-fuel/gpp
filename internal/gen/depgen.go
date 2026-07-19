package gen

import (
	"go/ast"
	"strings"

	"goforge.dev/gpp/internal/core"
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
func processDeps(f *sourceFile, pkgPath string, totals map[*ast.FuncDecl]bool, plan *enumPlan) ([]lower.Edit, []*registry.DepFn, []diag.Diagnostic) {
	fileHasLinear := false
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
		indexedSig := false
		checkIndexed := func(fl *ast.FieldList) {
			if fl == nil {
				return
			}
			for _, fld := range fl.List {
				base, args := instantiationOf(text(fld.Type, fld.Type))
				if base == "" {
					continue
				}
				if idxPos, arity, ok := plan.isIndexed(base); ok && len(args) == arity && len(idxPos) > 0 {
					indexedSig = true
				}
				// Imported indexed enums are unknown here, but a
				// term-shaped argument marks the instantiation (walk-2's
				// rule); the marker preserves the unerased signature.
				for _, a := range args {
					if termShapedText(a) {
						indexedSig = true
					}
				}
			}
		}
		checkIndexed(fd.Type.Params)
		checkIndexed(fd.Type.Results)
		if !hasQuantity && len(natIdents) == 0 && !indexedSig {
			continue
		}
		if fd.Recv != nil {
			errf(fd, "a dependent signature cannot have a receiver in v0.7.0")
			continue
		}
		eqOK := true
		for _, p := range params {
			if base, _ := instantiationOf(p.typeText); base == "Eq" && p.quantity != "0" {
				errf(p.name, "a proof parameter (%s) must be erased: give %s quantity 0", p.typeText, p.name.Name)
				eqOK = false
			}
		}
		if !eqOK {
			continue
		}

		// Multiplicity variables: `[m mult]` binders erase from the
		// type-parameter list; every non-numeric quantity must name one.
		multVars := map[string]bool{}
		if tp := fd.Type.TypeParams; tp != nil {
			var multFields []*ast.Field
			for _, fld := range tp.List {
				if id, isID := fld.Type.(*ast.Ident); isID && id.Name == "mult" {
					multFields = append(multFields, fld)
					for _, n := range fld.Names {
						multVars[n.Name] = true
					}
				}
			}
			if len(multFields) == len(tp.List) && len(multFields) > 0 {
				edits = append(edits, lower.Edit{Start: src.Offset(tp.Opening), End: src.Offset(tp.Closing) + 1, New: ""})
			} else {
				for i, fld := range tp.List {
					if id, isID := fld.Type.(*ast.Ident); !isID || id.Name != "mult" {
						continue
					}
					start, end := src.Offset(fld.Pos()), src.Offset(fld.End())
					if i+1 < len(tp.List) {
						end = src.Offset(tp.List[i+1].Pos())
					} else if i > 0 {
						start = src.Offset(tp.List[i-1].End())
					}
					edits = append(edits, lower.Edit{Start: start, End: end, New: ""})
				}
			}
		}
		quantities := map[string]string{}
		badQ := false
		for _, p := range params {
			if p.quantity == "" {
				continue
			}
			if p.quantity != "0" && p.quantity != "1" && !multVars[p.quantity] {
				errf(p.name, "quantity %s of parameter %s is not 0, 1, or a declared multiplicity variable ([%s mult])", p.quantity, p.name.Name, p.quantity)
				badQ = true
				continue
			}
			quantities[p.name.Name] = p.quantity
		}
		if badQ {
			continue
		}
		for _, qerr := range checkQuantities(fd, quantities) {
			errf(fd, "%v", qerr)
		}

		// Linear params (quantity 1): the erased parameter travels as a
		// use-once cell (`1 f T` becomes `f Lin[T]`) and every value use
		// in the body takes through it — the static checker proved
		// exactly-once per path, so whichever occurrence executes is the
		// single take.
		for _, p := range params {
			if p.quantity != "1" {
				continue
			}
			if _, variadic := p.field.Type.(*ast.Ellipsis); variadic {
				errf(p.name, "a variadic parameter cannot be linear in v0.7.0 (each element would need its own cell); use a slice or a multiplicity variable")
				continue
			}
			fileHasLinear = true
			edits = append(edits,
				lower.Edit{Start: src.Offset(p.field.Type.Pos()), End: src.Offset(p.field.Type.Pos()), New: "Lin["},
				lower.Edit{Start: src.Offset(p.field.Type.End()), End: src.Offset(p.field.Type.End()), New: "]"})
			if fd.Body != nil {
				for _, use := range valueUses(fd.Body, p.name.Name) {
					at := src.Offset(use.End())
					edits = append(edits, lower.Edit{Start: at, End: at, New: ".Use()"})
				}
			}
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
		droppedIdx := map[int]bool{}
		for i, p := range params {
			if p.quantity == "0" {
				droppedIdx[i] = true
			}
		}
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
			} else if i > 0 && !droppedIdx[i-1] {
				// Last parameter: consume the preceding comma — unless
				// the previous parameter is also dropped (its own edit
				// already consumed the separator).
				start = src.Offset(params[i-1].field.End())
			}
			edits = append(edits, lower.Edit{Start: start, End: end, New: ""})
		}
		if ast.IsExported(fd.Name.Name) && fd.Body != nil {
			var gps []guardParam
			for _, p := range params {
				if p.quantity == "0" {
					continue // erased: not present at runtime
				}
				gps = append(gps, guardParam{name: p.name.Name, typeText: p.typeText})
			}
			edits = append(edits, guardEdits(f, fd, gps, plan)...)
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
	if fileHasLinear {
		end := len(src.Src)
		edits = append(edits, lower.Edit{Start: end, End: end, New: linCellText})
	}
	return edits, deps, diags
}

// guardParam is one parameter considered for runtime guards.
type guardParam struct {
	name     string
	typeText string
}

// guardEdits synthesizes runtime precondition checks for one exported
// dependent function: a parameter typed at an indexed-enum instantiation
// whose index makes a variant IMPOSSIBLE gets a fail-fast type check —
// gpp callers proved the index statically; plain-Go callers panic with a
// precise message instead of computing garbage.
func guardEdits(f *sourceFile, fd *ast.FuncDecl, params []guardParam, plan *enumPlan) []lower.Edit {
	src := f.gpp
	var guards []string
	for _, p := range params {
		base, argTexts := instantiationOf(p.typeText)
		if base == "" {
			continue
		}
		var enum *registry.Enum
		for _, m := range plan.models {
			if m.Name == base && len(m.Indices) > 0 {
				enum = m
			}
		}
		if enum == nil || len(argTexts) != len(enum.TParams)+len(enum.Indices) {
			continue
		}
		idxPos := map[int]bool{}
		for _, ib := range enum.Indices {
			idxPos[ib.Pos] = true
		}
		var idxTerms, typeArgs []string
		for i, a := range argTexts {
			if idxPos[i] {
				idxTerms = append(idxTerms, a)
			} else {
				typeArgs = append(typeArgs, a)
			}
		}
		tagOf := planTagOf(plan)
		for _, v := range enum.Variants {
			if len(v.IndexArgs) != len(idxTerms) {
				continue
			}
			impossible := false
			for i := range idxTerms {
				if core.IndexClash(idxTerms[i], v.IndexArgs[i], tagOf) {
					impossible = true
				}
			}
			if !impossible {
				continue
			}
			head := v.TypeName
			var targs []string
			for _, oi := range v.OccursIn(enum) {
				if oi < len(typeArgs) {
					targs = append(targs, typeArgs[oi])
				}
			}
			if len(targs) > 0 {
				head += "[" + strings.Join(targs, ", ") + "]"
			}
			guards = append(guards, "\tif _, ok := any("+p.name+").("+head+"); ok {\n\t\tpanic(\"gpp: "+fd.Name.Name+": "+p.name+" with index "+strings.Join(idxTerms, ", ")+" cannot be "+v.Name+"\")\n\t}")
		}
	}
	if len(guards) == 0 {
		return nil
	}
	at := src.Offset(fd.Body.Lbrace) + 1
	return []lower.Edit{{Start: at, End: at, New: "\n" + strings.Join(guards, "\n")}}
}

// instantiationOf splits "Vec[T, n+1]" into base name and argument
// texts ("" base when not an instantiation).
func instantiationOf(text string) (string, []string) {
	open := strings.IndexByte(text, '[')
	if open <= 0 || !strings.HasSuffix(text, "]") {
		return "", nil
	}
	base := strings.TrimSpace(text[:open])
	for _, r := range base {
		if !(r == '_' || r == '.' || (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || (r >= '0' && r <= '9')) {
			return "", nil
		}
	}
	if i := strings.LastIndexByte(base, '.'); i >= 0 {
		base = base[i+1:]
	}
	var args []string
	for _, a := range splitTopLevelText(text[open+1:len(text)-1], ',') {
		args = append(args, strings.TrimSpace(a))
	}
	return base, args
}

// splitTopLevelText splits on a separator at bracket/paren depth zero.
func splitTopLevelText(s string, sep byte) []string {
	var out []string
	depth, start := 0, 0
	for i := 0; i < len(s); i++ {
		switch s[i] {
		case '[', '(':
			depth++
		case ']', ')':
			depth--
		case sep:
			if depth == 0 {
				out = append(out, s[start:i])
				start = i + 1
			}
		}
	}
	out = append(out, s[start:])
	return out
}

// termShapedText reports whether an argument text can only be a term.
func termShapedText(a string) bool {
	if a == "" {
		return false
	}
	if a[0] >= '0' && a[0] <= '9' {
		return true
	}
	return strings.ContainsAny(a, "+-*()")
}

// planTagOf builds a tag table over the package's index domains.
func planTagOf(plan *enumPlan) func(string) (string, bool) {
	return func(name string) (string, bool) {
		for _, m := range plan.models {
			if len(m.TParams) != 0 || len(m.Indices) != 0 {
				continue
			}
			for _, v := range m.Variants {
				if v.Name == name {
					return m.Name, true
				}
			}
		}
		return "", false
	}
}

// linCellText is the per-file use-once cell backing linear values in
// erased Go. Plain-Go callers construct with LinOf and are policed; gpp
// callers proved the discipline statically. The cell is a bool, not an
// atomic: racing it requires two concurrent consumers — already a
// discipline violation — and sequential double use panics
// deterministically.
const linCellText = `

//gpp:once
// Lin carries a linear (use-exactly-once) value across the erased
// boundary; Use panics on reuse.
type Lin[T any] struct {
	v     T
	taken *bool
}

// LinOf wraps a value for a linear parameter.
func LinOf[T any](v T) Lin[T] { return Lin[T]{v: v, taken: new(bool)} }

// Use consumes the value; a second Use panics.
func (c Lin[T]) Use() T {
	if *c.taken {
		panic("gpp: linear value used more than once")
	}
	*c.taken = true
	return c.v
}
`

// valueUses collects value-position occurrences of name in a body
// (types and instantiation arguments are skipped — they erase).
func valueUses(body *ast.BlockStmt, name string) []*ast.Ident {
	var out []*ast.Ident
	var walk func(n ast.Node) bool
	walk = func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.ValueSpec:
			for _, v := range x.Values {
				ast.Inspect(v, walk)
			}
			return false
		case *ast.CompositeLit:
			for _, e := range x.Elts {
				ast.Inspect(e, walk)
			}
			return false
		case *ast.TypeAssertExpr:
			ast.Inspect(x.X, walk)
			return false
		case *ast.Ident:
			if x.Name == name {
				out = append(out, x)
			}
		}
		return true
	}
	ast.Inspect(body, walk)
	return out
}
