package resolve

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"sort"
	"strings"

	"golang.org/x/tools/go/packages"

	"goforge.dev/gpp/internal/diag"
	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/registry"
)

// fileResolver rewrites one shadow file for one fixpoint iteration.
type fileResolver struct {
	pkg         *packages.Package
	typesByPath map[string]*types.Package
	file        *ast.File
	src         []byte
	reg         *registry.Registry
	tokFile     *token.File

	parents map[ast.Node]ast.Node
	diags   []diag.Diagnostic
	edits   []lower.Edit

	// report enables give-up diagnostics. It is set only on the audit
	// pass after the fixpoint converges, so transient can't-resolve-yet
	// states never surface to the user.
	report bool
}

func (r *fileResolver) off(pos token.Pos) int { return r.tokFile.Offset(pos) }

func (r *fileResolver) text(from, to token.Pos) string {
	return string(r.src[r.off(from):r.off(to)])
}

func (r *fileResolver) errorf(pos token.Pos, format string, args ...any) {
	r.diags = append(r.diags, diag.At(posOf(r.pkg.Fset, pos), format, args...))
}

// resolve finds and rewrites every resolvable candidate in the file,
// returning a non-overlapping edit set (nested candidates defer to the next
// fixpoint iteration).
func (r *fileResolver) resolve() ([]lower.Edit, []diag.Diagnostic) {
	r.parents = map[ast.Node]ast.Node{}
	var stack []ast.Node
	ast.Inspect(r.file, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return false
		}
		if len(stack) > 0 {
			r.parents[n] = stack[len(stack)-1]
		}
		stack = append(stack, n)
		return true
	})

	ast.Inspect(r.file, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.SelectorExpr:
			r.candidate(x)
			r.ctorCandidate(x)
		case *ast.Ident:
			r.ctorCandidate(x)
		case *ast.TypeSwitchStmt:
			r.matchCandidate(x)
		}
		return true
	})

	// Drop edits that overlap an earlier-accepted edit (outer-vs-inner
	// call chains); the fixpoint picks the rest up next iteration.
	sort.SliceStable(r.edits, func(i, j int) bool { return r.edits[i].Start < r.edits[j].Start })
	var kept []lower.Edit
	prevEnd := -1
	for _, e := range r.edits {
		if e.Start < prevEnd {
			continue
		}
		kept = append(kept, e)
		prevEnd = e.End
	}
	return kept, r.diags
}

// candidate inspects one selector expression and rewrites it if it is a
// use of a registered generic method.
func (r *fileResolver) candidate(sel *ast.SelectorExpr) {
	info := r.pkg.TypesInfo
	if !r.reg.HasMethodName(sel.Sel.Name) {
		return
	}
	// A real selection (field or actual method) always wins — superset
	// semantics: valid Go keeps its Go meaning.
	if _, isReal := info.Selections[sel]; isReal {
		return
	}
	if info.Uses[sel.Sel] != nil {
		return // qualified identifier (pkg.Name) or otherwise resolved
	}
	if id, ok := sel.X.(*ast.Ident); ok {
		if _, isPkg := info.Uses[id].(*types.PkgName); isPkg {
			return
		}
	}
	tv, ok := info.Types[sel.X]
	if !ok {
		return // receiver not yet typed; a later iteration will see it
	}

	// Find the method: directly on the receiver's type, on the enum a
	// variant struct belongs to (Some(41).Map(f)), or promoted through
	// embedded fields.
	var h *hit
	if m, named, ok := lookupDirect(r.reg, tv.Type, sel.Sel.Name); ok {
		_, wasPtr := asNamed(tv.Type)
		h = &hit{method: m, named: named, finalPtr: wasPtr}
	} else if m, named, e, ok := r.lookupViaVariant(tv.Type, sel.Sel.Name); ok {
		_, wasPtr := asNamed(tv.Type)
		h = &hit{method: m, named: named, finalPtr: wasPtr, viaEnum: e}
	} else {
		promoted, perr := promote(r.reg, tv.Type, sel.Sel.Name)
		if perr != nil {
			r.errorf(sel.Pos(), "%v", perr)
			return
		}
		if promoted == nil {
			return // not a gpp method use; the backstop will judge it
		}
		h = promoted
	}

	// Classify the syntactic context.
	switch p := r.parents[sel].(type) {
	case *ast.CallExpr:
		if p.Fun == sel {
			r.rewriteCall(p, sel, nil, h, tv)
			return
		}
	case *ast.IndexExpr:
		if p.X == sel {
			r.instantiated(p, sel, []ast.Expr{p.Index}, h, tv)
			return
		}
	case *ast.IndexListExpr:
		if p.X == sel {
			r.instantiated(p, sel, p.Indices, h, tv)
			return
		}
	}
	// Bare method value. A method with no type parameters of its own (an
	// enum method) needs no instantiation — lower it directly. Generic
	// methods keep Go's rule for uninstantiated generic function values.
	if h.method.NumMethodTParams == 0 {
		r.methodValue(sel, sel, nil, h, tv)
		return
	}
	r.errorf(sel.Pos(), "cannot use generic method %s.%s as a value without instantiation (write %s.%s[...])",
		exprString(sel.X), sel.Sel.Name, exprString(sel.X), sel.Sel.Name)
}

// instantiated handles s.Map[int](f) and the method value s.Map[int].
func (r *fileResolver) instantiated(idx ast.Expr, sel *ast.SelectorExpr, typeArgs []ast.Expr, h *hit, tv types.TypeAndValue) {
	if call, ok := r.parents[idx].(*ast.CallExpr); ok && call.Fun == idx {
		r.rewriteCall(call, sel, typeArgs, h, tv)
		return
	}
	r.methodValue(idx, sel, typeArgs, h, tv)
}

// receiverArg renders the receiver argument text, applying Go's automatic
// &/* rules against the lowered function's explicit first parameter.
func (r *fileResolver) receiverArg(sel *ast.SelectorExpr, h *hit, tv types.TypeAndValue) (string, bool) {
	text := r.text(sel.X.Pos(), sel.X.End())
	if needsParen(sel.X) {
		text = "(" + text + ")"
	}
	if len(h.path) > 0 {
		text = text + "." + strings.Join(h.path, ".")
	}
	// exprIsPtr: does the (possibly path-extended) receiver expression
	// denote a pointer to the declaring type?
	exprIsPtr := h.finalPtr
	// addressable: can we take its address if the method wants a pointer?
	addressable := tv.Addressable() || h.throughPtr

	if h.method.Pointer {
		if exprIsPtr {
			return text, true
		}
		if !addressable {
			r.errorf(sel.Pos(), "cannot call pointer method %s on %s", sel.Sel.Name, types.TypeString(tv.Type, nil))
			return "", false
		}
		return "&" + text, true
	}
	if exprIsPtr {
		return "*" + text, true
	}
	return text, true
}

// rewriteCall rewrites a method call to the lowered function call.
func (r *fileResolver) rewriteCall(call *ast.CallExpr, sel *ast.SelectorExpr, typeArgs []ast.Expr, h *hit, tv types.TypeAndValue) {
	recvArg, ok := r.receiverArg(sel, h, tv)
	if !ok {
		return
	}
	funcRef, ok := r.funcRef(sel.Pos(), h.method)
	if !ok {
		return
	}

	var targsText string
	if len(typeArgs) > 0 {
		// Go requires prefix instantiation: receiver type arguments (from
		// the receiver's static type) come before the explicit ones.
		recvTargs, ok := r.receiverTypeArgs(sel.Pos(), h)
		if !ok {
			return
		}
		explicit := r.text(typeArgs[0].Pos(), typeArgs[len(typeArgs)-1].End())
		all := append(recvTargs, explicit)
		targsText = "[" + strings.Join(all, ", ") + "]"
	}

	argsText := ""
	if len(call.Args) > 0 {
		argsText = ", " + r.text(call.Args[0].Pos(), argEnd(call))
	}
	r.edits = append(r.edits, lower.Edit{
		Start: r.off(call.Pos()),
		End:   r.off(call.End()),
		New:   funcRef + targsText + "(" + recvArg + argsText + ")",
	})
}

// lookupViaVariant finds an enum method when the receiver is a variant
// struct (which implements the enum interface).
func (r *fileResolver) lookupViaVariant(t types.Type, methodName string) (*registry.Method, *types.Named, *registry.Enum, bool) {
	named, _ := asNamed(t)
	if named == nil || named.Obj().Pkg() == nil {
		return nil, nil, nil, false
	}
	e, ok := r.reg.EnumByVariantType(named.Obj().Pkg().Path(), named.Obj().Name())
	if !ok {
		return nil, nil, nil, false
	}
	m, ok := r.reg.Lookup(e.PkgPath, e.Name, methodName)
	if !ok {
		return nil, nil, nil, false
	}
	return m, named, e, true
}

// receiverTypeArgs renders the receiver's type arguments for prefix
// instantiation.
func (r *fileResolver) receiverTypeArgs(at token.Pos, h *hit) ([]string, bool) {
	if h.method.NumRecvTParams == 0 {
		return nil, true
	}
	if h.viaEnum != nil {
		// Variant-struct receiver: rebuild the enum's type arguments from
		// the variant's kept arguments plus its ground result positions.
		v := variantByTypeName(h.viaEnum, h.named.Obj().Name())
		if v == nil {
			return nil, false
		}
		out := make([]string, len(h.viaEnum.TParams))
		if v.ResultArgs != nil {
			for i, arg := range v.ResultArgs {
				out[i] = arg
			}
		}
		kept := keptIndices(h.viaEnum, v)
		ta := h.named.TypeArgs()
		if ta == nil || ta.Len() != len(kept) {
			return nil, false
		}
		for i, ki := range kept {
			text, err := r.typeText(ta.At(i))
			if err != nil {
				r.errorf(at, "%v", err)
				return nil, false
			}
			out[ki] = text
		}
		return out, true
	}
	targs := h.named.TypeArgs()
	if targs == nil || targs.Len() != h.method.NumRecvTParams {
		got := 0
		if targs != nil {
			got = targs.Len()
		}
		r.errorf(at, "internal error: receiver %s has %d type arguments, expected %d",
			h.named.Obj().Name(), got, h.method.NumRecvTParams)
		return nil, false
	}
	out := make([]string, targs.Len())
	for i := 0; i < targs.Len(); i++ {
		text, err := r.typeText(targs.At(i))
		if err != nil {
			r.errorf(at, "%v", err)
			return nil, false
		}
		out[i] = text
	}
	return out, true
}

// funcRef renders a reference to the lowered function, qualified when it
// lives in another package.
func (r *fileResolver) funcRef(at token.Pos, m *registry.Method) (string, bool) {
	if m.PkgPath == r.pkg.PkgPath {
		return m.FuncName, true
	}
	name, ok := r.importName(m.PkgPath)
	if !ok {
		r.errorf(at, "using %s requires importing %q", m.Origin(), m.PkgPath)
		return "", false
	}
	return name + "." + m.FuncName, true
}

// importName finds the file-local name of an imported package.
func (r *fileResolver) importName(pkgPath string) (string, bool) {
	for _, imp := range r.file.Imports {
		path := strings.Trim(imp.Path.Value, `"`)
		if path != pkgPath {
			continue
		}
		if imp.Name != nil {
			if imp.Name.Name == "_" || imp.Name.Name == "." {
				return "", false
			}
			return imp.Name.Name, true
		}
		if tp, ok := r.typesByPath[pkgPath]; ok {
			return tp.Name(), true
		}
		return "", false
	}
	return "", false
}

// typeText renders a type in this file's namespace.
func (r *fileResolver) typeText(t types.Type) (string, error) {
	var missing error
	qual := func(p *types.Package) string {
		if p == r.pkg.Types {
			return ""
		}
		if name, ok := r.importName(p.Path()); ok {
			return name
		}
		missing = fmt.Errorf("type %s requires importing %q; add the import or restructure the call",
			types.TypeString(t, nil), p.Path())
		return p.Name()
	}
	text := types.TypeString(t, qual)
	return text, missing
}

// argEnd returns the end of the last argument, including a variadic "...".
func argEnd(call *ast.CallExpr) token.Pos {
	end := call.Args[len(call.Args)-1].End()
	if call.Ellipsis.IsValid() {
		end = call.Ellipsis + 3
	}
	return end
}

func needsParen(e ast.Expr) bool {
	switch e.(type) {
	case *ast.Ident, *ast.SelectorExpr, *ast.IndexExpr, *ast.IndexListExpr,
		*ast.CallExpr, *ast.ParenExpr, *ast.CompositeLit, *ast.BasicLit:
		return false
	}
	return true
}

func exprString(e ast.Expr) string {
	switch x := e.(type) {
	case *ast.Ident:
		return x.Name
	case *ast.SelectorExpr:
		return exprString(x.X) + "." + x.Sel.Name
	}
	return "expression"
}
