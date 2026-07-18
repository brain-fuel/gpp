package resolve

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"strings"

	"goforge.dev/gpp/internal/directive"
	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/registry"
)

// Class structure resolution (v0.5.0): witness flattening (leaves-first,
// diamonds collapsing), upcast generation, and instance default filling.
// All candidates are idempotent by AST inspection.

// classFor recognizes a witness struct decl by its //gpp:class marker.
func (r *fileResolver) classFor(gd *ast.GenDecl) (*registry.Class, *ast.TypeSpec, *ast.StructType, bool) {
	if gd.Tok != token.TYPE || len(gd.Specs) != 1 || gd.Doc == nil {
		return nil, nil, nil, false
	}
	ts, ok := gd.Specs[0].(*ast.TypeSpec)
	if !ok {
		return nil, nil, nil, false
	}
	st, ok := ts.Type.(*ast.StructType)
	if !ok {
		return nil, nil, nil, false
	}
	for _, c := range gd.Doc.List {
		if m, mok := directive.ParseClassMarker(c.Text); mok && m.Name == ts.Name.Name {
			cls, found := r.reg.LookupClass(registry.ClassRef{PkgPath: r.pkg.PkgPath, Name: ts.Name.Name})
			if !found {
				return nil, nil, nil, false
			}
			return cls, ts, st, true
		}
	}
	return nil, nil, nil, false
}

// classCandidate flattens embedded ancestor witnesses and appends upcast
// methods once flat.
func (r *fileResolver) classCandidate(gd *ast.GenDecl) {
	cls, _, st, ok := r.classFor(gd)
	if !ok {
		return
	}
	info := r.pkg.TypesInfo

	// Existing named fields (for dedupe) and embedded fields (to flatten).
	named := map[string]ast.Expr{}
	var embedded []*ast.Field
	for _, f := range st.Fields.List {
		if len(f.Names) == 0 {
			embedded = append(embedded, f)
		}
		for _, n := range f.Names {
			named[n.Name] = f.Type
		}
	}

	flattenedAny := false
	for _, field := range embedded {
		tv, typed := info.Types[field.Type]
		if !typed || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
			if r.report {
				r.errorf(field.Type.Pos(), "unknown embedded class in %s", cls.Name)
			}
			continue
		}
		anc, _ := types.Unalias(tv.Type).(*types.Named)
		if anc == nil {
			if r.report {
				r.errorf(field.Type.Pos(), "class %s can only embed classes; %s is not a class witness", cls.Name, r.localTypeString(tv.Type))
			}
			continue
		}
		under, _ := anc.Underlying().(*types.Struct)
		if under == nil {
			continue
		}
		// Leaves-first: wait until the ancestor itself is flat.
		flat := true
		for i := 0; i < under.NumFields(); i++ {
			if under.Field(i).Embedded() {
				flat = false
			}
		}
		if !flat {
			continue
		}
		var lines []string
		conflict := false
		for i := 0; i < under.NumFields(); i++ {
			fld := under.Field(i)
			ft, err := r.typeText(fld.Type())
			if err != nil {
				r.errorf(field.Type.Pos(), "%v", err)
				conflict = true
				break
			}
			if existing, dup := named[fld.Name()]; dup {
				// Diamond collapse: identical text keeps one copy;
				// conflicting signatures are an error.
				etext := r.text(existing.Pos(), existing.End())
				if normalizeSig(etext) != normalizeSig(ft) {
					r.errorf(field.Type.Pos(), "class %s inherits %s with conflicting signatures", cls.Name, fld.Name())
					conflict = true
					break
				}
				continue
			}
			named[fld.Name()] = nil
			lines = append(lines, fld.Name()+" "+ft)
		}
		if conflict {
			continue
		}
		r.edits = append(r.edits, lower.Edit{
			Start: r.off(field.Pos()),
			End:   r.off(field.End()),
			New:   strings.Join(lines, "\n"),
		})
		flattenedAny = true
	}
	if flattenedAny || len(embedded) > 0 {
		return // upcasts wait for a flat struct
	}

	// Flat: append missing upcast methods.
	ref := registry.ClassRef{PkgPath: cls.PkgPath, Name: cls.Name}
	for _, anc := range r.reg.Ancestors(ref) {
		method := "As" + anc.Name
		if r.fileHasMethod(cls.Name, method) {
			continue
		}
		text, ok := r.upcastText(cls, anc)
		if !ok {
			continue
		}
		end := len(r.src)
		r.edits = append(r.edits, lower.Edit{Start: end, End: end, New: "\n" + text})
	}
}

// normalizeSig canonicalizes a field-type text for diamond comparison.
func normalizeSig(s string) string {
	return strings.Join(strings.Fields(s), " ")
}

// fileHasMethod reports whether this file declares recvType.method.
func (r *fileResolver) fileHasMethod(recvType, method string) bool {
	for _, decl := range r.file.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Recv == nil || fd.Name.Name != method || len(fd.Recv.List) == 0 {
			continue
		}
		t := fd.Recv.List[0].Type
		for {
			switch x := t.(type) {
			case *ast.StarExpr:
				t = x.X
				continue
			case *ast.IndexExpr:
				t = x.X
				continue
			case *ast.IndexListExpr:
				t = x.X
				continue
			}
			break
		}
		if id, isID := t.(*ast.Ident); isID && id.Name == recvType {
			return true
		}
	}
	return false
}

// upcastText renders one AsAncestor method from the ancestor's flat
// witness fields.
func (r *fileResolver) upcastText(cls *registry.Class, anc registry.ClassRef) (string, bool) {
	ancPkg := r.typesByPath[anc.PkgPath]
	if ancPkg == nil {
		return "", false
	}
	tn, _ := ancPkg.Scope().Lookup(anc.Name).(*types.TypeName)
	if tn == nil {
		return "", false
	}
	ancNamed, _ := tn.Type().(*types.Named)
	if ancNamed == nil {
		return "", false
	}
	under, _ := ancNamed.Underlying().(*types.Struct)
	if under == nil {
		return "", false
	}
	for i := 0; i < under.NumFields(); i++ {
		if under.Field(i).Embedded() {
			return "", false // ancestor not flat yet
		}
	}
	ancText, ok := r.witnessTypeText(anc, cls.TParam)
	if !ok {
		return "", false
	}
	var assigns []string
	for i := 0; i < under.NumFields(); i++ {
		n := under.Field(i).Name()
		assigns = append(assigns, fmt.Sprintf("%s: m.%s", n, n))
	}
	recvType := cls.Name + "[" + cls.TParam + "]"
	return fmt.Sprintf(
		"// As%s views the %s witness as its %s part.\nfunc (m %s) As%s() %s {\n\treturn %s{%s}\n}\n",
		anc.Name, cls.Name, anc.Name, recvType, anc.Name, ancText, ancText, strings.Join(assigns, ", ")), true
}

// instanceCandidate validates an instance constructor and fills omitted
// defaulted operations with lazy closures (the receiver view is rebuilt
// at call time, so defaults always see the completed witness).
func (r *fileResolver) instanceCandidate(decl ast.Node, doc *ast.CommentGroup) {
	if doc == nil {
		return
	}
	var inst *registry.Instance
	for _, c := range doc.List {
		if m, ok := directive.ParseInstanceMarker(c.Text); ok {
			inst, _ = r.reg.LookupInstance(r.pkg.PkgPath, m.Name)
			break
		}
	}
	if inst == nil {
		return
	}
	ref := inst.Class
	allOps := r.reg.AllOps(ref)
	defaults := r.reg.AllDefaults(ref)

	// Locate `w := &C[…]{…}` and `return *w`.
	var lit *ast.CompositeLit
	var wName string
	var retPos ast.Node
	ast.Inspect(decl, func(n ast.Node) bool {
		if lit != nil && retPos != nil {
			return false
		}
		if as, ok := n.(*ast.AssignStmt); ok && len(as.Lhs) == 1 && len(as.Rhs) == 1 {
			if un, isUn := as.Rhs[0].(*ast.UnaryExpr); isUn {
				if cl, isCl := un.X.(*ast.CompositeLit); isCl {
					if id, isID := as.Lhs[0].(*ast.Ident); isID {
						lit, wName = cl, id.Name
					}
				}
			}
		}
		if ret, ok := n.(*ast.ReturnStmt); ok && len(ret.Results) == 1 {
			if star, isStar := ret.Results[0].(*ast.StarExpr); isStar {
				if _, isID := star.X.(*ast.Ident); isID {
					retPos = ret
				}
			}
		}
		return true
	})
	if lit == nil || retPos == nil {
		return
	}

	// Validate literal fields and collect what is present.
	present := map[string]bool{}
	for _, el := range lit.Elts {
		kv, ok := el.(*ast.KeyValueExpr)
		if !ok {
			continue
		}
		key, ok := kv.Key.(*ast.Ident)
		if !ok {
			continue
		}
		if _, known := allOps[key.Name]; !known {
			r.errorf(key.Pos(), "class %s has no operation %s", ref.Name, key.Name)
			return
		}
		present[key.Name] = true
	}
	// Already-assigned defaults (idempotence).
	ast.Inspect(decl, func(n ast.Node) bool {
		as, ok := n.(*ast.AssignStmt)
		if !ok || len(as.Lhs) != 1 {
			return true
		}
		if sel, isSel := as.Lhs[0].(*ast.SelectorExpr); isSel {
			if id, isID := sel.X.(*ast.Ident); isID && id.Name == wName {
				present[sel.Sel.Name] = true
			}
		}
		return true
	})

	// Missing ops: defaulted ones fill; the rest are errors.
	witType := r.pkg.TypesInfo.Types[lit.Type]
	var fills []string
	opNames := sortedOpNames(allOps)
	for _, op := range opNames {
		if present[op] {
			continue
		}
		declClass, hasDefault := defaults[op]
		if !hasDefault {
			r.errorf(decl.Pos(), "instance %s does not implement %s: missing operation %s (and %s declares no default)",
				inst.Name, ref.Name, op, ref.Name)
			return
		}
		if witType.Type == nil || witType.Type == types.Typ[types.Invalid] {
			return // wait for the witness type
		}
		fill, ok := r.defaultFillText(wName, op, declClass, ref, witType.Type)
		if !ok {
			return // wait (signature or upcast not ready)
		}
		fills = append(fills, fill)
	}
	if len(fills) == 0 {
		return
	}
	at := r.off(retPos.Pos())
	for at > 0 && r.src[at-1] != '\n' {
		at--
	}
	r.edits = append(r.edits, lower.Edit{Start: at, End: at, New: strings.Join(fills, "\n") + "\n"})
}

func sortedOpNames(ops map[string]registry.ClassRef) []string {
	out := make([]string, 0, len(ops))
	for n := range ops {
		out = append(out, n)
	}
	for i := 1; i < len(out); i++ {
		for j := i; j > 0 && out[j] < out[j-1]; j-- {
			out[j], out[j-1] = out[j-1], out[j]
		}
	}
	return out
}

// defaultFillText renders `w.Op = func(…) … { return view.DefaultOp(…) }`.
func (r *fileResolver) defaultFillText(w, op string, declClass, instClass registry.ClassRef, witType types.Type) (string, bool) {
	obj, _, _ := types.LookupFieldOrMethod(witType, true, r.pkg.Types, op)
	v, _ := obj.(*types.Var)
	if v == nil {
		return "", false
	}
	sig, _ := types.Unalias(v.Type()).(*types.Signature)
	if sig == nil {
		return "", false
	}
	var params, args []string
	for i := 0; i < sig.Params().Len(); i++ {
		pt, err := r.typeText(sig.Params().At(i).Type())
		if err != nil {
			return "", false
		}
		name := fmt.Sprintf("__gpp_a%d", i)
		if sig.Variadic() && i == sig.Params().Len()-1 {
			elem, _ := types.Unalias(sig.Params().At(i).Type()).(*types.Slice)
			if elem == nil {
				return "", false
			}
			et, err := r.typeText(elem.Elem())
			if err != nil {
				return "", false
			}
			params = append(params, name+" ..."+et)
			args = append(args, name+"...")
			continue
		}
		params = append(params, name+" "+pt)
		args = append(args, name)
	}
	var results []string
	for i := 0; i < sig.Results().Len(); i++ {
		rt, err := r.typeText(sig.Results().At(i).Type())
		if err != nil {
			return "", false
		}
		results = append(results, rt)
	}
	retText := ""
	switch len(results) {
	case 0:
	case 1:
		retText = " " + results[0]
	default:
		retText = " (" + strings.Join(results, ", ") + ")"
	}
	view := w
	if declClass != instClass {
		// The default lives on an ancestor: go through the upcast, which
		// must exist by now (same package or distributed).
		view = w + ".As" + declClass.Name + "()"
	}
	callText := view + ".Default" + op + "(" + strings.Join(args, ", ") + ")"
	body := callText
	if len(results) > 0 {
		body = "return " + callText
	}
	return fmt.Sprintf("%s.%s = func(%s)%s { %s }", w, op, strings.Join(params, ", "), retText, body), true
}
