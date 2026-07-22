package resolve

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"go/types"
	"reflect"
	"strings"
	"unicode"

	"goforge.dev/goplus/internal/registry"
	"goforge.dev/goplus/internal/syntax"
)

// Chain-mode match lowering: when any pattern nests, the whole type-switch
// skeleton is regenerated as an order-preserving block chain — type
// switches cannot fall through on a failed nested check, and two arms may
// share a head constructor:
//
//	{
//		__gp_m0 := any(e)
//		{
//			__gp_a0, __gp_k0 := any(__gp_m0).(Add)
//			if __gp_k0 {
//				__gp_a1, __gp_k1 := any(__gp_a0.L).(Lit)
//				if __gp_k1 {
//					a := __gp_a1.V
//					<body verbatim>
//					goto __gp_match0_done
//				}
//			}
//		}
//		…
//		panic("goplus: impossible enum value in match")
//	__gp_match0_done:
//		;
//	}

// chainEmit renders the full replacement text for a nested-mode match.
func (r *fileResolver) chainEmit(sw *ast.TypeSwitchStmt, varName string, subjText string, arms []*armAnalysis, hasWildcard bool) string {
	idx := strings.TrimPrefix(varName, "__gp_m")
	done := fmt.Sprintf("__gp_match%s_done", idx)
	var b strings.Builder
	b.WriteString("{\n")
	fmt.Fprintf(&b, "%s := any(%s)\n", varName, subjText)
	ctorArms := false
	for _, arm := range arms {
		if !arm.pat.wild {
			ctorArms = true
		}
	}
	if !ctorArms {
		fmt.Fprintf(&b, "_ = %s\n", varName)
	}

	// Arms whose bodies terminate (return/panic/goto) never reach the
	// join label; omitting their gotos — and the label entirely when no
	// arm falls through — preserves Go's termination analysis, so a match
	// whose arms all return still counts as a terminating statement.
	needLabel := false
	for _, arm := range arms {
		if !stmtsTerminate(arm.clause.Body) {
			needLabel = true
		}
	}

	temps := 0
	for _, arm := range arms {
		gotoDone := ""
		if !stmtsTerminate(arm.clause.Body) {
			gotoDone = done
		}
		b.WriteString("{\n")
		if arm.pat.wild {
			b.WriteString(arm.body)
			if gotoDone != "" {
				fmt.Fprintf(&b, "\ngoto %s\n", gotoDone)
			} else {
				b.WriteString("\n")
			}
		} else {
			r.chainPattern(&b, arm, varName, &temps, gotoDone)
		}
		b.WriteString("}\n")
	}
	if !hasWildcard {
		b.WriteString("panic(\"goplus: impossible enum value in match\")\n")
	}
	if needLabel {
		fmt.Fprintf(&b, "%s:\n;\n", done)
	}
	b.WriteString("}")
	return b.String()
}

// stmtsTerminate conservatively reports whether a statement list always
// transfers control (return, panic, goto, or an if/else or block that
// does on every path).
func stmtsTerminate(stmts []ast.Stmt) bool {
	if len(stmts) == 0 {
		return false
	}
	return stmtTerminates(stmts[len(stmts)-1])
}

func stmtTerminates(s ast.Stmt) bool {
	switch st := s.(type) {
	case *ast.ReturnStmt:
		return true
	case *ast.BranchStmt:
		return st.Tok == token.GOTO
	case *ast.ExprStmt:
		if call, ok := st.X.(*ast.CallExpr); ok {
			if id, ok := call.Fun.(*ast.Ident); ok && id.Name == "panic" {
				return true
			}
		}
	case *ast.BlockStmt:
		return stmtsTerminate(st.List)
	case *ast.IfStmt:
		if st.Else == nil {
			return false
		}
		return stmtTerminates(st.Body) && stmtTerminates(st.Else)
	case *ast.LabeledStmt:
		return stmtTerminates(st.Stmt)
	}
	return false
}

// chainPattern renders one constructor arm's assert ladder. gotoDone is
// empty when the arm's body always terminates (no join jump needed).
func (r *fileResolver) chainPattern(b *strings.Builder, arm *armAnalysis, rootVal string, temps *int, gotoDone string) {
	var bindings []string
	closers := 0
	ok := r.emitPatChecks(b, arm.pat, rootVal, temps, &bindings, &closers, arm.binderName, arm.body)
	if !ok {
		return
	}
	for _, bind := range bindings {
		b.WriteString(bind + "\n")
	}
	b.WriteString(arm.body)
	if gotoDone != "" {
		fmt.Fprintf(b, "\ngoto %s\n", gotoDone)
	} else {
		b.WriteString("\n")
	}
	for i := 0; i < closers; i++ {
		b.WriteString("}\n")
	}
}

// emitPatChecks recursively emits assert-and-test lines for a pattern.
func (r *fileResolver) emitPatChecks(b *strings.Builder, p *rpat, val string, temps *int, bindings *[]string, closers *int, binder, bodyText string) bool {
	head, headOK := r.rpatCaseType(p, p.col.pos)
	if !headOK {
		return false
	}
	// The asserted value is needed only when something binds or a nested
	// pattern selects a field; otherwise blank it to keep go/types happy.
	needVal := binder != "" && identReferencedInText(bodyText, binder)
	for _, argPat := range p.args {
		if argPat.binder != "" && identReferencedInText(bodyText, argPat.binder) {
			needVal = true
		}
		if argPat.variant != nil {
			needVal = true
		}
	}
	a := "_"
	if needVal {
		a = fmt.Sprintf("__gp_a%d", *temps)
	}
	k := fmt.Sprintf("__gp_k%d", *temps)
	*temps++
	fmt.Fprintf(b, "%s, %s := any(%s).(%s)\n", a, k, val, head)
	fmt.Fprintf(b, "if %s {\n", k)
	*closers++
	if binder != "" && identReferencedInText(bodyText, binder) {
		*bindings = append(*bindings, fmt.Sprintf("%s := %s", binder, a))
	}
	for i, argPat := range p.args {
		field := a + "." + p.variant.Params[i].FieldName
		switch {
		case argPat.wild:
		case argPat.binder != "":
			if identReferencedInText(bodyText, argPat.binder) {
				*bindings = append(*bindings, fmt.Sprintf("%s := %s", argPat.binder, field))
			}
		default:
			if !r.emitPatChecks(b, argPat, field, temps, bindings, closers, "", bodyText) {
				return false
			}
		}
	}
	return true
}

// rpatCaseType renders the (instantiated, possibly package-qualified)
// struct type a pattern node asserts to.
func (r *fileResolver) rpatCaseType(p *rpat, at token.Pos) (string, bool) {
	name := p.variant.TypeName
	if p.col.enum.PkgPath != r.pkg.PkgPath {
		alias, ok := r.importName(p.col.enum.PkgPath)
		if !ok {
			r.errorf(token.NoPos, "matching %s requires importing %q", p.col.enum.Name, p.col.enum.PkgPath)
			return "", false
		}
		name = alias + "." + name
	}
	occ := p.variant.OccursIn(p.col.enum)
	if len(occ) == 0 {
		return name, true
	}
	bind, ok := variantSubst(p.col.enum, p.variant, p.col.targs)
	if !ok {
		r.errorf(at, "pattern %s cannot be matched against %s[%s]: the type arguments do not determine the variant's type parameters under Go's erasure; match on a scrutinee whose type reveals them, or use 'case _:'",
			p.variant.Name, p.col.enum.Name, strings.Join(p.col.targs, ", "))
		return "", false
	}
	return name + "[" + strings.Join(structArgs(p.col.enum, p.variant, bind), ", ") + "]", true
}

// enumColFromTypeText resolves a field's type text (in declaring-package
// terms, already instantiated) to a pattern column.
func (r *fileResolver) enumColFromTypeText(declPkg, text string) patCol {
	expr, err := parser.ParseExpr(text)
	if err != nil {
		return patCol{}
	}
	var baseName string
	var args []ast.Expr
	switch t := expr.(type) {
	case *ast.Ident:
		baseName = t.Name
	case *ast.IndexExpr:
		if id, ok := t.X.(*ast.Ident); ok {
			baseName = id.Name
			args = []ast.Expr{t.Index}
		}
	case *ast.IndexListExpr:
		if id, ok := t.X.(*ast.Ident); ok {
			baseName = id.Name
			args = t.Indices
		}
	case *ast.SelectorExpr:
		// Qualified enum from another package: resolvable only when the
		// qualifier is importable here; treat as opaque otherwise.
		return patCol{}
	}
	if baseName == "" {
		return patCol{}
	}
	e, ok := r.reg.LookupEnum(declPkg, baseName)
	if !ok {
		return patCol{}
	}
	col := patCol{enum: e}
	for _, a := range args {
		var buf bytes.Buffer
		printer.Fprint(&buf, token.NewFileSet(), a)
		col.targs = append(col.targs, buf.String())
	}
	return col
}

// substTypeTextLite substitutes identifiers in a type expression's text —
// the resolve-side twin of gen's substituteTypeText.
func substTypeTextLite(text string, subst map[string]string) (string, error) {
	if len(subst) != 0 {
		clean := make(map[string]string, len(subst))
		for from, to := range subst {
			if strings.TrimSpace(to) != from {
				clean[from] = to
			}
		}
		subst = clean
	}
	if len(subst) == 0 {
		return text, nil
	}
	for from, to := range subst {
		if containsTypeIdentifier(to, from) {
			// Substitution is simultaneous, not recursive. Walking a newly
			// inserted `n+1` while replacing n would otherwise grow forever.
			return substTypeIdentifiers(text, subst), nil
		}
	}
	expr, err := parser.ParseExpr(text)
	if err != nil {
		// Dependent index terms are intentionally richer than Go type
		// arguments: Rule[T, PredicateAtomID(id)] is valid Go+ marker text but
		// not a Go expression because a call cannot appear as a Go type
		// argument. Fall back to token-wise identifier substitution.
		return substTypeIdentifiers(text, subst), nil
	}
	repl := map[string]ast.Expr{}
	for from, to := range subst {
		re, rerr := parser.ParseExpr(to)
		if rerr != nil {
			return "", rerr
		}
		repl[from] = re
	}
	if id, ok := expr.(*ast.Ident); ok {
		if to, hit := subst[id.Name]; hit {
			return to, nil
		}
	}
	skip := map[*ast.Ident]bool{}
	ast.Inspect(expr, func(n ast.Node) bool {
		switch node := n.(type) {
		case *ast.SelectorExpr:
			skip[node.Sel] = true
		case *ast.CallExpr:
			// A bare total-function name can coincide with a dependent
			// parameter (for example Atom's `id` and PredicateAtomID).
			// Only call arguments are substitutable terms; the callee name is
			// part of the signature's vocabulary.
			if id, ok := node.Fun.(*ast.Ident); ok {
				skip[id] = true
			}
		case *ast.Field:
			for _, nm := range node.Names {
				skip[nm] = true
			}
		}
		return true
	})
	exprType := reflect.TypeOf((*ast.Expr)(nil)).Elem()
	swap := func(v reflect.Value) {
		if !v.CanSet() || v.IsNil() {
			return
		}
		if id, ok := v.Interface().(*ast.Ident); ok && !skip[id] {
			if re, hit := repl[id.Name]; hit {
				v.Set(reflect.ValueOf(re))
			}
		}
	}
	ast.Inspect(expr, func(n ast.Node) bool {
		if n == nil {
			return false
		}
		rv := reflect.ValueOf(n)
		if rv.Kind() != reflect.Pointer || rv.IsNil() {
			return true
		}
		rv = rv.Elem()
		if rv.Kind() != reflect.Struct {
			return true
		}
		for i := 0; i < rv.NumField(); i++ {
			fv := rv.Field(i)
			switch {
			case fv.Type() == exprType:
				swap(fv)
			case fv.Kind() == reflect.Slice && fv.Type().Elem() == exprType:
				for j := 0; j < fv.Len(); j++ {
					swap(fv.Index(j))
				}
			}
		}
		return true
	})
	var buf bytes.Buffer
	if err := printer.Fprint(&buf, token.NewFileSet(), expr); err != nil {
		return "", err
	}
	return buf.String(), nil
}

func containsTypeIdentifier(text, target string) bool {
	runes := []rune(text)
	for i := 0; i < len(runes); {
		if runes[i] != '_' && !unicode.IsLetter(runes[i]) {
			i++
			continue
		}
		start := i
		for i++; i < len(runes) && (runes[i] == '_' || unicode.IsLetter(runes[i]) || unicode.IsDigit(runes[i])); i++ {
		}
		if string(runes[start:i]) == target {
			return true
		}
	}
	return false
}

func substTypeIdentifiers(text string, subst map[string]string) string {
	runes := []rune(text)
	var out strings.Builder
	for i := 0; i < len(runes); {
		if runes[i] != '_' && !unicode.IsLetter(runes[i]) {
			out.WriteRune(runes[i])
			i++
			continue
		}
		start := i
		for i++; i < len(runes) && (runes[i] == '_' || unicode.IsLetter(runes[i]) || unicode.IsDigit(runes[i])); i++ {
		}
		name := string(runes[start:i])
		next := i
		for next < len(runes) && unicode.IsSpace(runes[next]) {
			next++
		}
		prev := start - 1
		for prev >= 0 && unicode.IsSpace(runes[prev]) {
			prev--
		}
		to, replace := subst[name]
		// Selector fields and bare callees are vocabulary, not variables.
		if replace && !((prev >= 0 && runes[prev] == '.') || (next < len(runes) && runes[next] == '(')) {
			out.WriteString(to)
		} else {
			out.WriteString(name)
		}
	}
	return out.String()
}

func typesIdentical(a, b types.Type) bool { return types.Identical(a, b) }

// rpat is a semantically resolved pattern node.
type rpat struct {
	wild    bool
	binder  string // bare-name field binder (leaf); "" otherwise
	variant *registry.EnumVariant
	col     patCol // column instance this node matches against
	args    []*rpat
}

// normPat renders an rpat back to a normalized PatNode (binders → wilds,
// names → Go+ variant names) for the usefulness engine.
func normPat(p *rpat) (out syntax.PatNode) {
	if p.wild || p.binder != "" {
		return syntax.PatNode{Wild: true}
	}
	out = syntax.PatNode{Name: p.variant.Name, HasArgs: len(p.args) > 0}
	for _, a := range p.args {
		n := normPat(a)
		out.Args = append(out.Args, n)
	}
	return out
}

// resolveRPat resolves a textual pattern against a column, applying the
// "a constructor name shadows binding" rule to bare names.
func (r *fileResolver) resolveRPat(node syntax.PatNode, col patCol, topLevel bool, tparamNames map[string]bool) (*rpat, string) {
	if node.Wild {
		return &rpat{wild: true, col: col}, ""
	}
	if col.enum == nil {
		if node.HasArgs || node.Qual != "" {
			return nil, fmt.Sprintf("pattern %s cannot match here: the value is not an enum", node.String())
		}
		if topLevel {
			return nil, fmt.Sprintf("pattern %s cannot match here: the value is not an enum", node.String())
		}
		return &rpat{binder: node.Name, col: col}, ""
	}
	// Qualifier plausibility.
	if node.Qual != "" && node.Qual != col.enum.Name {
		if alias, ok := r.importName(col.enum.PkgPath); !ok || alias != node.Qual {
			return nil, fmt.Sprintf("pattern %s does not name a variant of %s", node.String(), col.enum.Name)
		}
	}
	v, isVariant := col.enum.Variant(node.Name)
	if !isVariant {
		for _, cand := range col.enum.Variants {
			if cand.TypeName == node.Name {
				v, isVariant = cand, true
				break
			}
		}
	}
	if !isVariant {
		if node.HasArgs || node.Qual != "" || topLevel {
			return nil, fmt.Sprintf("%s is not a variant of %s", node.Name, col.enum.Name)
		}
		return &rpat{binder: node.Name, col: col}, ""
	}
	rp := &rpat{variant: v, col: col}
	if node.HasArgs && len(node.Args) != len(v.Params) {
		return nil, fmt.Sprintf("pattern %s has %d fields but %s declares %d",
			node.String(), len(node.Args), v.Name, len(v.Params))
	}
	if !node.HasArgs && len(v.Params) > 0 {
		return nil, fmt.Sprintf("pattern %s must bind %d fields (or use %s(_%s))",
			v.Name, len(v.Params), v.Name, strings.Repeat(", _", len(v.Params)-1))
	}
	u := &usefulCtx{r: r, tparamNames: tparamNames}
	fieldCols := u.fieldColumns(col, v)
	for i, argNode := range node.Args {
		child, errMsg := r.resolveRPat(argNode, fieldCols[i], false, tparamNames)
		if errMsg != "" {
			return nil, errMsg
		}
		rp.args = append(rp.args, child)
	}
	return rp, ""
}
