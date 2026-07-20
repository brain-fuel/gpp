package resolve

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"strings"

	"goforge.dev/goplus/internal/directive"
	"goforge.dev/goplus/internal/lower"
)

// Delegation forwarders (v0.6.0). A struct field marked `delegate` (its
// //goplus:delegate marker survives pass 1) must have an interface type; the
// outer type gains a generated value-receiver forwarder for every
// interface method it does not otherwise declare — authored anywhere in
// the package, promoted from embedding, or generated in a previous
// iteration all count as overrides. Two delegate fields offering one
// method is a hard error. A delegate field is NOT embedded: no promotion
// happens beyond the generated forwarders.

// delegateCandidate generates missing forwarders for one struct decl.
func (r *fileResolver) delegateCandidate(gd *ast.GenDecl) {
	if gd.Tok != token.TYPE || len(gd.Specs) != 1 {
		return
	}
	ts, ok := gd.Specs[0].(*ast.TypeSpec)
	if !ok {
		return
	}
	st, ok := ts.Type.(*ast.StructType)
	if !ok {
		return
	}
	type delegateField struct {
		field *ast.Field
		name  string
		iface *types.Interface
	}
	var dfs []delegateField
	for _, f := range st.Fields.List {
		if f.Doc == nil || len(f.Names) == 0 {
			continue
		}
		marked := false
		for _, c := range f.Doc.List {
			if strings.TrimSpace(c.Text) == directive.DelegatePrefix {
				marked = true
			}
		}
		if !marked {
			continue
		}
		tv, typed := r.pkg.TypesInfo.Types[f.Type]
		if !typed || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
			return // wait for the field type
		}
		iface, isIface := types.Unalias(tv.Type).Underlying().(*types.Interface)
		if !isIface {
			if r.report {
				r.errorf(f.Type.Pos(), "delegate field %s of %s must have an interface type; %s is %s",
					f.Names[0].Name, ts.Name.Name, r.text(f.Type.Pos(), f.Type.End()), r.localTypeString(tv.Type))
			}
			return
		}
		for _, n := range f.Names {
			dfs = append(dfs, delegateField{field: f, name: n.Name, iface: iface})
		}
	}
	if len(dfs) == 0 {
		return
	}

	// The outer type's declared methods (authored, promoted, previously
	// generated).
	obj := r.pkg.TypesInfo.Defs[ts.Name]
	named, _ := obj.(*types.TypeName)
	if named == nil {
		return
	}
	nt, _ := named.Type().(*types.Named)
	if nt == nil {
		return
	}
	declared := map[string]bool{}
	for _, ms := range []*types.MethodSet{types.NewMethodSet(nt), types.NewMethodSet(types.NewPointer(nt))} {
		for i := 0; i < ms.Len(); i++ {
			declared[ms.At(i).Obj().Name()] = true
		}
	}

	// Overlap check among the methods no one declares.
	owner := map[string]string{}
	for _, df := range dfs {
		for i := 0; i < df.iface.NumMethods(); i++ {
			m := df.iface.Method(i)
			if declared[m.Name()] {
				continue
			}
			if prev, dup := owner[m.Name()]; dup && prev != df.name {
				if r.report {
					r.errorf(ts.Pos(), "type %s delegates %s through both %s and %s; declare %s on %s to take ownership",
						ts.Name.Name, m.Name(), prev, df.name, m.Name(), ts.Name.Name)
				}
				return
			}
			owner[m.Name()] = df.name
		}
	}

	// Receiver rendering.
	recvType := ts.Name.Name
	var tparamNames []string
	if ts.TypeParams != nil {
		for _, f := range ts.TypeParams.List {
			for _, n := range f.Names {
				tparamNames = append(tparamNames, n.Name)
			}
		}
		recvType += "[" + strings.Join(tparamNames, ", ") + "]"
	}
	recv := strings.ToLower(ts.Name.Name[:1])
	for _, tn := range tparamNames {
		if strings.EqualFold(tn, recv) {
			recv = "x"
		}
	}

	for _, df := range dfs {
		for i := 0; i < df.iface.NumMethods(); i++ {
			m := df.iface.Method(i)
			if declared[m.Name()] {
				continue
			}
			if !m.Exported() && (m.Pkg() == nil || m.Pkg().Path() != r.pkg.PkgPath) {
				if r.report {
					r.errorf(df.field.Pos(), "cannot delegate %s: interface %s has unexported method %s from package %s",
						df.name, r.text(df.field.Type.Pos(), df.field.Type.End()), m.Name(), m.Pkg().Path())
				}
				return
			}
			if r.fileHasMethod(ts.Name.Name, m.Name()) {
				continue // same-iteration idempotence guard
			}
			text, ok := r.forwarderText(ts.Name.Name, recvType, recv, df.name, m)
			if !ok {
				return
			}
			end := len(r.src)
			r.edits = append(r.edits, lower.Edit{Start: end, End: end, New: "\n" + text})
			declared[m.Name()] = true
		}
	}
}

// forwarderText renders one generated forwarding method.
func (r *fileResolver) forwarderText(typeName, recvType, recv, fieldName string, m *types.Func) (string, bool) {
	sig, _ := m.Type().(*types.Signature)
	if sig == nil {
		return "", false
	}
	var params, args []string
	for i := 0; i < sig.Params().Len(); i++ {
		pt := sig.Params().At(i).Type()
		name := fmt.Sprintf("p%d", i)
		if sig.Variadic() && i == sig.Params().Len()-1 {
			sl, _ := types.Unalias(pt).(*types.Slice)
			if sl == nil {
				return "", false
			}
			et, err := r.typeText(sl.Elem())
			if err != nil {
				r.errorf(m.Pos(), "%v", err)
				return "", false
			}
			params = append(params, name+" ..."+et)
			args = append(args, name+"...")
			continue
		}
		tt, err := r.typeText(pt)
		if err != nil {
			r.errorf(m.Pos(), "%v", err)
			return "", false
		}
		params = append(params, name+" "+tt)
		args = append(args, name)
	}
	var results []string
	for i := 0; i < sig.Results().Len(); i++ {
		rt, err := r.typeText(sig.Results().At(i).Type())
		if err != nil {
			r.errorf(m.Pos(), "%v", err)
			return "", false
		}
		results = append(results, rt)
	}
	resText := ""
	switch len(results) {
	case 0:
	case 1:
		resText = " " + results[0]
	default:
		resText = " (" + strings.Join(results, ", ") + ")"
	}
	call := fmt.Sprintf("%s.%s.%s(%s)", recv, fieldName, m.Name(), strings.Join(args, ", "))
	body := call
	if len(results) > 0 {
		body = "return " + call
	}
	return fmt.Sprintf("%s %s.%s\nfunc (%s %s) %s(%s)%s { %s }\n",
		directive.DelegatePrefix, typeName, fieldName,
		recv, recvType, m.Name(), strings.Join(params, ", "), resText, body), true
}
