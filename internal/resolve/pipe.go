package resolve

import (
	"fmt"
	"go/ast"
	"go/types"
	"strings"

	"goforge.dev/gpp/internal/lower"
)

// Bare pipeline segments. Pass 1 lowers `x |> Map(f)` to the carrier
// `__gpp_bare_Map(x, f)`; once the head's type is known, this resolver
// decides member-vs-function per the locked policy: both resolving is a
// hard error with the two explicit spellings (`.Map(f)` member,
// `Map(_, f)` function); a tuple-typed head follows Go's spread rule.

// pipeCandidate inspects a call whose callee carries the bare-segment
// marker.
func (r *fileResolver) pipeCandidate(call *ast.CallExpr) {
	name, brackets, ok := carrierParts(r, call.Fun)
	if !ok || len(call.Args) == 0 {
		return
	}
	info := r.pkg.TypesInfo
	head := call.Args[0]
	tv, typed := info.Types[head]
	if !typed || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
		if r.report {
			r.errorf(call.Pos(), "cannot resolve this pipeline segment: the type of the piped value is unknown")
		}
		return
	}

	headText := r.text(head.Pos(), head.End())
	segArgsText := ""
	if len(call.Args) > 1 {
		segArgsText = r.text(call.Args[1].Pos(), argEnd(call))
	}

	// Multi-result head: Go's spread rule, uniformly.
	if tup, isTuple := tv.Type.(*types.Tuple); isTuple {
		r.pipeSpread(call, name, brackets, tup, headText, segArgsText)
		return
	}

	// Member candidate: full Go selector semantics plus gpp methods.
	member := false
	obj, _, _ := types.LookupFieldOrMethod(tv.Type, tv.Addressable(), r.pkg.Types, name)
	switch o := obj.(type) {
	case *types.Func:
		member = true
	case *types.Var:
		if _, isSig := o.Type().Underlying().(*types.Signature); isSig {
			member = true // func-typed field
		}
	}
	gppHit, perr := r.memberHit(tv.Type, name)
	if perr != nil {
		r.errorf(call.Pos(), "%v", perr)
		return
	}
	if gppHit != nil {
		if gppHit.method.Pointer && !gppHit.finalPtr && !(tv.Addressable() || gppHit.throughPtr) {
			gppHit = nil // pointer method on non-addressable head: not a candidate
		}
	}
	member = member || gppHit != nil

	// Function candidate: lexical scope (locals shadow), builtins,
	// conversions, indexed function values; plus local constructors.
	var fnObj types.Object
	if scope := r.pkg.Types.Scope().Innermost(call.Pos()); scope != nil {
		_, fnObj = scope.LookupParent(name, call.Pos())
	}
	fn := false
	fnKind := ""
	switch o := fnObj.(type) {
	case *types.Func:
		fn = true
	case *types.Builtin:
		fn = true
	case *types.TypeName:
		// A conversion candidate — unless the type IS a lowered variant
		// struct, in which case the constructor reading owns it.
		if o.Pkg() == nil {
			fn = true
		} else if _, isVariant := r.reg.EnumByVariantType(o.Pkg().Path(), o.Name()); !isVariant {
			fn, fnKind = true, "conversion"
		}
	case *types.Var:
		if _, isSig := o.Type().Underlying().(*types.Signature); isSig || brackets != "" {
			fn = true // func value, or an indexable value like fs[0]
		} else {
			fnKind = fmt.Sprintf("a variable of type %s, not a function", r.localTypeString(o.Type()))
		}
	}
	_ = fnKind
	ctors := r.reg.EnumsByVariantName(r.pkg.PkgPath, name)
	ctor := len(ctors) > 0

	segFor := func(kind string) string {
		// Render the explicit spelling for the diagnostic.
		if kind == "member" {
			return "." + name + brackets + "(" + segArgsText + ")"
		}
		if segArgsText == "" {
			return name + brackets + "(_)"
		}
		return name + brackets + "(_, " + segArgsText + ")"
	}

	switch {
	case member && fn:
		r.errorf(call.Pos(), "%s is both a method of %s and a function in this package; write %s for the method or %s for the function",
			name, r.localTypeString(tv.Type), segFor("member"), segFor("function"))
	case member && ctor:
		r.errorf(call.Pos(), "%s is both a method of %s and a constructor of %s; write %s for the method or qualify the constructor: %s.%s",
			name, r.localTypeString(tv.Type), ctors[0].Name, segFor("member"), ctors[0].Name, name)
	case fn && ctor:
		r.errorf(call.Pos(), "%s is both a function in this package and a constructor of %s; qualify the constructor: %s.%s or pipe with %s for the function",
			name, ctors[0].Name, ctors[0].Name, name, segFor("function"))
	case member:
		text := headText
		if needsParen(head) {
			text = "(" + text + ")"
		}
		insertion := text + "." + name + brackets + "(" + segArgsText + ")"
		r.edits = append(r.edits, lower.Edit{Start: r.off(call.Pos()), End: r.off(call.End()), New: insertion})
	case fn && !ctor && func() bool {
		// Railway: a plain-function stage on a Result head lifts by shape.
		T, E, isRes := r.isResult(tv.Type)
		if !isRes {
			return false
		}
		var sig *types.Signature
		switch o := fnObj.(type) {
		case *types.Func:
			sig, _ = o.Type().(*types.Signature)
		case *types.Var:
			sig, _ = types.Unalias(o.Type().Underlying()).(*types.Signature)
		}
		if sig == nil {
			return false // builtin or conversion: direct
		}
		return r.railwayBare(call, name, brackets, T, E, sig)
	}():
		// handled by railwayBare (edit or diagnostic already recorded)
	case fn || ctor:
		insertion := name + brackets + "(" + headText
		if segArgsText != "" {
			insertion += ", " + segArgsText
		}
		insertion += ")"
		r.edits = append(r.edits, lower.Edit{Start: r.off(call.Pos()), End: r.off(call.End()), New: insertion})
	default:
		msg := fmt.Sprintf("%s is neither a method of %s nor a function in scope", name, r.localTypeString(tv.Type))
		if fnObj != nil && fnKind != "" && fnKind != "conversion" {
			msg += " (" + name + " is " + fnKind + ")"
		}
		r.errorf(call.Pos(), "%s", msg)
	}
}

// pipeSpread applies Go's spread rule to a tuple-typed head: the segment
// must have no other arguments and the function must take exactly the
// tuple.
func (r *fileResolver) pipeSpread(call *ast.CallExpr, name, brackets string, tup *types.Tuple, headText, segArgsText string) {
	if segArgsText != "" {
		r.errorf(call.Pos(), "cannot pipe the %d results of %s into %s: the segment has other arguments, so the results cannot spread",
			tup.Len(), headText, name)
		return
	}
	var fnObj types.Object
	if scope := r.pkg.Types.Scope().Innermost(call.Pos()); scope != nil {
		_, fnObj = scope.LookupParent(name, call.Pos())
	}
	var sig *types.Signature
	switch o := fnObj.(type) {
	case *types.Func:
		sig, _ = o.Type().(*types.Signature)
	case *types.Var:
		sig, _ = o.Type().Underlying().(*types.Signature)
	}
	if sig == nil {
		r.errorf(call.Pos(), "cannot pipe the %d results of %s into %s; pipelines carry a single value unless the results spread into a matching function",
			tup.Len(), headText, name)
		return
	}
	ok := sig.Params().Len() == tup.Len() && !sig.Variadic()
	if ok {
		for i := 0; i < tup.Len(); i++ {
			if !types.AssignableTo(tup.At(i).Type(), sig.Params().At(i).Type()) {
				ok = false
				break
			}
		}
	}
	if !ok {
		want := make([]string, sig.Params().Len())
		for i := range want {
			want[i] = r.localTypeString(sig.Params().At(i).Type())
		}
		r.errorf(call.Pos(), "cannot pipe the %d results of %s into %s (want %s)",
			tup.Len(), headText, name, strings.Join(want, ", "))
		return
	}
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(call.Pos()),
		End:   r.off(call.End()),
		New:   name + brackets + "(" + headText + ")",
	})
}

// carrierParts strips the bare-segment marker from a carrier callee.
func carrierParts(r *fileResolver, fun ast.Expr) (name, brackets string, ok bool) {
	switch fn := fun.(type) {
	case *ast.Ident:
		if rest, found := strings.CutPrefix(fn.Name, lower.BareCarrierPrefix); found {
			return rest, "", true
		}
	case *ast.IndexExpr:
		if id, isID := fn.X.(*ast.Ident); isID {
			if rest, found := strings.CutPrefix(id.Name, lower.BareCarrierPrefix); found {
				return rest, r.text(fn.Lbrack, fn.Rbrack+1), true
			}
		}
	case *ast.IndexListExpr:
		if id, isID := fn.X.(*ast.Ident); isID {
			if rest, found := strings.CutPrefix(id.Name, lower.BareCarrierPrefix); found {
				return rest, r.text(fn.Lbrack, fn.Rbrack+1), true
			}
		}
	}
	return "", "", false
}
