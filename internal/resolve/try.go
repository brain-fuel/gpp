package resolve

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"regexp"
	"strconv"
	"strings"

	"goforge.dev/gpp/internal/lower"
)

// Postfix `?` propagation (v0.4.0). Pass 1 lowers `e?` to the carrier
// `__gpp_try<N>(e)`; resolution hoists an early-return before the
// enclosing statement once the operand and the enclosing function are
// typed:
//
//	data := os.ReadFile(path)?
//	⇒ data, __gpp_err0 := os.ReadFile(path)
//	  if __gpp_err0 != nil {
//	  	return *new(R1), …, __gpp_err0        // (…, error) enclosing
//	  }
//
// A Result-returning enclosing function returns Err instead — via
// result.Unpack when its error type is exactly `error`, or a variant
// assertion that preserves the typed error otherwise.

var tryCarrier = regexp.MustCompile(`^__gpp_try(\d+)$`)

// operand shapes
type tryShape int

const (
	tryResult tryShape = iota // Result[T, E]
	tryTuple                  // (T1..Tk, error) call
	tryError                  // bare error
)

// enclosing shapes
type fnShape int

const (
	fnGoError fnShape = iota // (R1..Rm, error)
	fnResult                 // Result[U, E2]
)

// tryCandidate lowers one __gpp_try<N>(op) carrier.
func (r *fileResolver) tryCandidate(call *ast.CallExpr) {
	fn, ok := call.Fun.(*ast.Ident)
	if !ok {
		return
	}
	m := tryCarrier.FindStringSubmatch(fn.Name)
	if m == nil || len(call.Args) != 1 {
		return
	}
	n, _ := strconv.Atoi(m[1])
	op := call.Args[0]

	// Inside an unresolved match skeleton the arm's binders and spans are
	// still in flux; wait for the match to expand first.
	if r.insideUnresolvedMatch(call) {
		return
	}

	info := r.pkg.TypesInfo
	tv, typed := info.Types[op]
	if !typed || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
		if r.report {
			r.errorf(call.Pos(), "cannot resolve this ?: the type of its operand is unknown")
		}
		return
	}

	// Operand shape.
	var (
		shape      tryShape
		vals       []types.Type // the values the operand yields (excl. error)
		resT, resE types.Type
	)
	switch t := tv.Type.(type) {
	case *types.Tuple:
		last := t.At(t.Len() - 1).Type()
		if !isErrorType(last) {
			r.errorf(op.Pos(), "the ? operand must be a Result value, an (…, error) call, or an error; this call's last result is %s", r.localTypeString(last))
			return
		}
		shape = tryTuple
		for i := 0; i < t.Len()-1; i++ {
			vals = append(vals, t.At(i).Type())
		}
	default:
		if T, E, isRes := r.isResult(tv.Type); isRes {
			shape, resT, resE = tryResult, T, E
			vals = []types.Type{T}
		} else if isErrorType(tv.Type) {
			shape = tryError
		} else {
			r.errorf(op.Pos(), "the ? operand must be a Result value, an (…, error) call, or an error; it has type %s", r.localTypeString(tv.Type))
			return
		}
	}

	// Enclosing function shape.
	sig, sigOK := r.enclosingSignature(call)
	if !sigOK {
		if r.report {
			r.errorf(call.Pos(), "cannot resolve this ?: the enclosing function's signature is unknown")
		}
		return
	}
	if sig == nil {
		r.errorf(call.Pos(), "expression if/switch/match and ? need an enclosing statement; use an init function for package-level values")
		return
	}
	res := sig.Results()
	var (
		encl     fnShape
		enclRets []types.Type // results before the trailing error (fnGoError)
		enclU    types.Type   // Result value type (fnResult)
		enclE    types.Type   // Result error type (fnResult)
	)
	switch {
	case res.Len() >= 1 && isErrorType(res.At(res.Len()-1).Type()):
		encl = fnGoError
		for i := 0; i < res.Len()-1; i++ {
			enclRets = append(enclRets, res.At(i).Type())
		}
	case res.Len() == 1:
		U, E2, isRes := r.isResult(res.At(0).Type())
		if !isRes {
			r.errorf(call.Pos(), "? cannot propagate failure here: the enclosing function returns neither (…, error) nor a Result")
			return
		}
		encl, enclU, enclE = fnResult, U, E2
	default:
		r.errorf(call.Pos(), "? cannot propagate failure here: the enclosing function returns neither (…, error) nor a Result")
		return
	}

	// Shape compatibility for Result-returning enclosings.
	if encl == fnResult {
		switch shape {
		case tryResult:
			if !isErrorType(enclE) && !types.Identical(resE, enclE) {
				r.errorf(op.Pos(), "cannot propagate a Result with error type %s from a function returning a Result with error type %s",
					r.localTypeString(resE), r.localTypeString(enclE))
				return
			}
		case tryTuple, tryError:
			if !isErrorType(enclE) {
				r.errorf(op.Pos(), "a (…, error)-shaped ? operand can only propagate into a function whose Result error type is error; this function's is %s", r.localTypeString(enclE))
				return
			}
		}
	}

	// Position legality up to the anchor.
	anchor, posOK := r.tryAnchor(call)
	if !posOK {
		return
	}
	if anchor == nil {
		r.errorf(call.Pos(), "expression if/switch/match and ? need an enclosing statement; use an init function for package-level values")
		return
	}

	// The failure branch's return statement.
	errName := fmt.Sprintf("__gpp_err%d", n)
	failReturn, frOK := r.tryFailReturn(call, encl, enclRets, enclU, enclE, errName)
	if !frOK {
		return
	}

	// Fast path: the carrier is the whole RHS of an assignment to
	// identifiers and the operand is a (…, error) call whose value count
	// matches — unpack in place.
	if shape == tryTuple {
		if as, isAssign := r.parents[call].(*ast.AssignStmt); isAssign &&
			as == anchor && len(as.Rhs) == 1 && as.Rhs[0] == call && len(as.Lhs) == len(vals) && identsOnly(as.Lhs) {
			opText := r.text(op.Pos(), op.End())
			var lhs []string
			for _, l := range as.Lhs {
				lhs = append(lhs, l.(*ast.Ident).Name)
			}
			lhs = append(lhs, errName)
			var b strings.Builder
			if as.Tok == token.DEFINE {
				fmt.Fprintf(&b, "%s := %s\n", strings.Join(lhs, ", "), opText)
			} else {
				fmt.Fprintf(&b, "var %s error\n%s = %s\n", errName, strings.Join(lhs, ", "), opText)
			}
			fmt.Fprintf(&b, "if %s != nil {\n%s\n}", errName, failReturn)
			r.edits = append(r.edits, lower.Edit{Start: r.off(as.Pos()), End: r.off(as.End()), New: b.String()})
			return
		}
		// Whole-return operand: return f()? with k matching the enclosing
		// value results.
		if ret, isRet := r.parents[call].(*ast.ReturnStmt); isRet &&
			ret == anchor && len(ret.Results) == 1 && ret.Results[0] == call && len(vals) > 1 {
			opText := r.text(op.Pos(), op.End())
			var names []string
			for i := range vals {
				names = append(names, fmt.Sprintf("__gpp_t%d_%d", n, i))
			}
			var b strings.Builder
			fmt.Fprintf(&b, "%s, %s := %s\n", strings.Join(names, ", "), errName, opText)
			fmt.Fprintf(&b, "if %s != nil {\n%s\n}\n", errName, failReturn)
			fmt.Fprintf(&b, "return %s", strings.Join(names, ", "))
			r.edits = append(r.edits, lower.Edit{Start: r.off(ret.Pos()), End: r.off(ret.End()), New: b.String()})
			return
		}
		if len(vals) > 1 {
			r.errorf(op.Pos(), "a ? operand returning %d values can only be the whole right-hand side of an assignment or the whole return operand", len(vals))
			return
		}
	}

	opText := r.text(op.Pos(), op.End())
	at := r.lineStartOff(r.off(anchor.Pos()))
	valName := fmt.Sprintf("__gpp_t%d", n)

	// Value-less operands propagate but produce nothing: only a statement
	// position can hold them.
	if len(vals) == 0 {
		es, isExprStmt := r.parents[call].(*ast.ExprStmt)
		if !isExprStmt || ast.Stmt(es) != anchor {
			r.errorf(op.Pos(), "this ? operand produces no value; use it as a statement")
			return
		}
		text := fmt.Sprintf("if %s := %s; %s != nil {\n%s\n}", errName, opText, errName, failReturn)
		r.edits = append(r.edits, lower.Edit{Start: r.off(es.Pos()), End: r.off(es.End()), New: text})
		return
	}

	var b strings.Builder
	switch {
	case shape == tryResult && encl == fnResult && !isErrorType(enclE):
		// Typed-error rail: variant assertion preserves E.
		resPkg, impOK := r.ensureResultImport()
		if !impOK {
			return
		}
		tText, tErr := r.typeText(resT)
		eText, eErr := r.typeText(resE)
		if tErr != nil || eErr != nil {
			if tErr == nil {
				tErr = eErr
			}
			r.errorf(op.Pos(), "%v", tErr)
			return
		}
		fmt.Fprintf(&b, "__gpp_r%d := %s\n", n, opText)
		fmt.Fprintf(&b, "if %s.IsErr(__gpp_r%d) {\n%s\n}\n", resPkg, n, failReturn)
		fmt.Fprintf(&b, "%s := any(__gpp_r%d).(%s.Ok[%s, %s]).Value", valName, n, resPkg, tText, eText)
	case shape == tryResult:
		resPkg, impOK := r.ensureResultImport()
		if !impOK {
			return
		}
		fmt.Fprintf(&b, "%s, %s := %s.Unpack(%s)\n", valName, errName, resPkg, opText)
		fmt.Fprintf(&b, "if %s != nil {\n%s\n}", errName, failReturn)
	default: // tryTuple with one value
		fmt.Fprintf(&b, "%s, %s := %s\n", valName, errName, opText)
		fmt.Fprintf(&b, "if %s != nil {\n%s\n}", errName, failReturn)
	}
	r.edits = append(r.edits, lower.Edit{Start: at, End: at, New: b.String() + "\n"})
	r.edits = append(r.edits, lower.Edit{Start: r.off(call.Pos()), End: r.off(call.End()), New: valName})
}

// tryFailReturn renders the return statement of a ?'s failure branch.
func (r *fileResolver) tryFailReturn(call *ast.CallExpr, encl fnShape, enclRets []types.Type, enclU, enclE types.Type, errName string) (string, bool) {
	shapeErr := errName
	if encl == fnGoError {
		var parts []string
		for _, rt := range enclRets {
			text, err := r.typeText(rt)
			if err != nil {
				r.errorf(call.Pos(), "%v", err)
				return "", false
			}
			parts = append(parts, "*new("+text+")")
		}
		parts = append(parts, shapeErr)
		return "return " + strings.Join(parts, ", "), true
	}
	resPkg, ok := r.ensureResultImport()
	if !ok {
		return "", false
	}
	uText, uErr := r.typeText(enclU)
	if uErr != nil {
		r.errorf(call.Pos(), "%v", uErr)
		return "", false
	}
	if isErrorType(enclE) {
		return fmt.Sprintf("return %s.Err[%s, error]{Err: %s}", resPkg, uText, errName), true
	}
	// Typed rail: the error value comes from the Err variant directly.
	eText, eErr := r.typeText(enclE)
	if eErr != nil {
		r.errorf(call.Pos(), "%v", eErr)
		return "", false
	}
	n := strings.TrimPrefix(errName, "__gpp_err")
	op := call.Args[0]
	tv := r.pkg.TypesInfo.Types[op]
	resT, resE, _ := r.isResult(tv.Type)
	tText, tErr := r.typeText(resT)
	if tErr != nil {
		r.errorf(call.Pos(), "%v", tErr)
		return "", false
	}
	_ = resE
	return fmt.Sprintf("return %s.Err[%s, %s]{Err: any(__gpp_r%s).(%s.Err[%s, %s]).Err}",
		resPkg, uText, eText, n, resPkg, tText, eText), true
}

// enclosingSignature finds the nearest enclosing function's signature.
// ok=false means it exists but is not typed yet; a nil signature with
// ok=true means package level.
func (r *fileResolver) enclosingSignature(n ast.Node) (*types.Signature, bool) {
	info := r.pkg.TypesInfo
	for node := r.parents[n]; node != nil; node = r.parents[node] {
		switch fn := node.(type) {
		case *ast.FuncDecl:
			obj := info.Defs[fn.Name]
			if obj == nil {
				return nil, false
			}
			sig, isSig := obj.Type().(*types.Signature)
			if !isSig {
				return nil, false
			}
			return sig, true
		case *ast.FuncLit:
			tv, typed := info.Types[fn]
			if !typed {
				return nil, false
			}
			sig, isSig := types.Unalias(tv.Type).(*types.Signature)
			if !isSig {
				return nil, false
			}
			return sig, true
		}
	}
	return nil, true
}

// tryAnchor finds the statement to hoist before, rejecting positions
// where an early return would change evaluation. A nil anchor with
// ok=true means package level.
func (r *fileResolver) tryAnchor(call *ast.CallExpr) (ast.Stmt, bool) {
	var n ast.Node = call
	for {
		p, ok := r.parents[n]
		if !ok {
			return nil, true
		}
		switch pp := p.(type) {
		case *ast.ForStmt:
			if n == pp.Cond || n == pp.Post {
				r.errorf(call.Pos(), "? cannot appear in a for condition or post statement; it would hoist outside the loop and evaluate only once")
				return nil, false
			}
		case *ast.IfStmt:
			if n == pp.Cond {
				if gp, isIf := r.parents[p].(*ast.IfStmt); isIf && gp.Else == p {
					r.errorf(call.Pos(), "? cannot appear in an else-if condition; it would hoist before the whole chain and always evaluate — nest the if statement instead")
					return nil, false
				}
			}
		case *ast.BinaryExpr:
			if (pp.Op == token.LAND || pp.Op == token.LOR) && n == pp.Y {
				r.errorf(call.Pos(), "? cannot appear on the right side of %s; it would hoist before the statement and always evaluate — use an if statement instead", pp.Op)
				return nil, false
			}
		case *ast.AssignStmt:
			for _, l := range pp.Lhs {
				if l == n {
					r.errorf(call.Pos(), "? cannot appear on the left side of an assignment")
					return nil, false
				}
			}
		case *ast.CaseClause:
			for _, v := range pp.List {
				if v == n {
					r.errorf(call.Pos(), "? cannot appear in a case value; case values evaluate in order only until one matches")
					return nil, false
				}
			}
		case *ast.CommClause:
			if n == pp.Comm {
				r.errorf(call.Pos(), "? cannot appear in a select communication clause")
				return nil, false
			}
		case *ast.DeferStmt:
			if n == ast.Node(pp.Call) {
				r.errorf(call.Pos(), "? cannot apply to a whole deferred call; the propagation would need to run at defer time — wrap the call in a function literal")
				return nil, false
			}
		case *ast.GoStmt:
			if n == ast.Node(pp.Call) {
				r.errorf(call.Pos(), "? cannot apply to a whole go call; wrap the call in a function literal")
				return nil, false
			}
		}
		if stmt, isStmt := p.(ast.Stmt); isStmt {
			switch r.parents[p].(type) {
			case *ast.BlockStmt, *ast.CaseClause, *ast.CommClause:
				return stmt, true
			}
		}
		n = p
	}
}

// insideUnresolvedMatch reports whether a node sits inside a match
// skeleton that still has unexpanded (case nil) arms.
func (r *fileResolver) insideUnresolvedMatch(n ast.Node) bool {
	for node := r.parents[n]; node != nil; node = r.parents[node] {
		sw, isSwitch := node.(*ast.TypeSwitchStmt)
		if !isSwitch {
			continue
		}
		if _, _, isSkel := skeletonGuard(sw); !isSkel {
			continue
		}
		for _, s := range sw.Body.List {
			c, isCase := s.(*ast.CaseClause)
			if !isCase {
				continue
			}
			for _, v := range c.List {
				if id, isID := v.(*ast.Ident); isID && id.Name == "nil" {
					return true
				}
			}
		}
	}
	return false
}

// ensureResultImport returns the local package name for
// goforge.dev/gpp/std/result, adding the import (one edit per file per
// iteration) when missing.
func (r *fileResolver) ensureResultImport() (string, bool) {
	for _, imp := range r.file.Imports {
		path, err := strconv.Unquote(imp.Path.Value)
		if err != nil || path != resultPkgPath {
			continue
		}
		if imp.Name != nil {
			if imp.Name.Name == "_" || imp.Name.Name == "." {
				continue
			}
			return imp.Name.Name, true
		}
		return resultPkgName, true
	}
	if r.resultImportName != "" {
		return r.resultImportName, true
	}
	name := resultPkgName
	if identNamedInFile(r.file, name) {
		name = "__gpp_result"
	}
	r.resultImportName = name
	alias := ""
	if name != resultPkgName {
		alias = name + " "
	}
	at := r.off(r.file.Name.End())
	r.edits = append(r.edits, lower.Edit{
		Start: at, End: at,
		New: fmt.Sprintf("\n\nimport %s%q", alias, resultPkgPath),
	})
	return name, true
}

const resultPkgName = "result"

// identNamedInFile reports whether an identifier with this name appears
// anywhere in the file (conservative shadow check for the import name).
func identNamedInFile(f *ast.File, name string) bool {
	found := false
	ast.Inspect(f, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok && id.Name == name {
			found = true
		}
		return !found
	})
	return found
}

func identsOnly(exprs []ast.Expr) bool {
	for _, e := range exprs {
		if _, ok := e.(*ast.Ident); !ok {
			return false
		}
	}
	return true
}

// isErrorType reports whether t is exactly the universe error interface.
func isErrorType(t types.Type) bool {
	return types.Identical(t, types.Universe.Lookup("error").Type())
}

// lineStartOff walks an offset back to the start of its line.
func (r *fileResolver) lineStartOff(off int) int {
	for off > 0 && r.src[off-1] != '\n' {
		off--
	}
	return off
}
