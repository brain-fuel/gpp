package resolve

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"strings"

	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/registry"
	"goforge.dev/gpp/internal/syntax"
)

// Match resolution. Pass 1 lowers each match to a type switch whose case
// heads are `case nil:` placeholders followed by `//gpp:pattern` carrier
// comments. Once the scrutinee's type is known, one pass resolves the
// whole match: case heads gain instantiated variant types, arms gain
// binding prologues, carriers are deleted (the progress signal), a sealed
// default-panic arm is added, and exhaustiveness and strictness rules are
// checked against the GADT-filtered variant universe.

// matchArm is one clause of a skeleton match under resolution.
type matchArm struct {
	clause   *ast.CaseClause
	pat      syntax.PatText
	carrier  [2]int // byte range of the carrier line (incl. newline)
	variant  *registry.EnumVariant
	wildcard bool
}

// matchCandidate inspects a type switch produced by lower.MatchSkeleton.
func (r *fileResolver) matchCandidate(sw *ast.TypeSwitchStmt) {
	varName, subj, ok := skeletonGuard(sw)
	if !ok {
		return
	}
	arms, allCarriers := r.collectArms(sw)
	if !allCarriers {
		return // already resolved (or not ours)
	}

	tv, ok := r.pkg.TypesInfo.Types[subj]
	if !ok || tv.Type == nil || tv.Type == types.Typ[types.Invalid] {
		return // scrutinee not typed yet; a later iteration will see it
	}
	named, _ := asNamed(tv.Type)
	var e *registry.Enum
	if named != nil && named.Obj().Pkg() != nil {
		e, _ = r.reg.LookupEnum(named.Obj().Pkg().Path(), named.Obj().Name())
	}
	if e == nil {
		if r.report {
			r.errorf(subj.Pos(), "match requires an enum-typed scrutinee; %s has type %s",
				r.text(subj.Pos(), subj.End()), r.localTypeString(tv.Type))
		}
		return
	}

	// Scrutinee type arguments, as render texts and as types.
	var targTexts []string
	var targTypes []types.Type
	if ta := named.TypeArgs(); ta != nil {
		for i := 0; i < ta.Len(); i++ {
			text, err := r.typeText(ta.At(i))
			if err != nil {
				r.errorf(subj.Pos(), "%v", err)
				return
			}
			targTexts = append(targTexts, text)
			targTypes = append(targTypes, ta.At(i))
		}
	}
	if len(targTexts) != len(e.TParams) {
		if r.report {
			r.errorf(subj.Pos(), "match scrutinee %s is not fully instantiated", e.Name)
		}
		return
	}

	// GADT filter: which variants can inhabit this instantiation?
	possible := map[string]bool{}
	for _, v := range e.Variants {
		possible[v.Name] = r.variantPossible(e, v, targTypes, targTexts)
	}

	// Resolve arms.
	matchPos := sw.Pos()
	failed := false
	fail := func(pos token.Pos, format string, args ...any) {
		r.errorf(pos, format, args...)
		failed = true
	}
	covered := map[string]bool{}
	sawWildcard := false
	totalBindings := 0
	type armPlan struct {
		arm      *matchArm
		head     string   // "default" or the instantiated case type
		bindings []string // prologue lines
	}
	var plans []armPlan

	for i, arm := range arms {
		if sawWildcard {
			fail(arm.clause.Case, "'case _:' must be the last arm of a match")
			break
		}
		if bad := bareBreak(arm.clause.Body); bad != token.NoPos {
			fail(bad, "break is not supported directly inside a match arm in v0.2.0; label the enclosing loop")
		}
		if arm.pat.Root.Wild {
			sawWildcard = true
			if i != len(arms)-1 {
				fail(arm.clause.Case, "'case _:' must be the last arm of a match")
			}
			plans = append(plans, armPlan{arm: arm, head: "default"})
			continue
		}
		v, verr := r.armVariant(e, arm)
		if verr != "" {
			fail(arm.clause.Case, "%s", verr)
			continue
		}
		arm.variant = v
		if !possible[v.Name] {
			fail(arm.clause.Case, "pattern %s can never match a value of type %s: %s constructs %s[%s]",
				arm.pat.Root.String(), r.localTypeString(tv.Type), v.Name, e.Name, strings.Join(v.ResultArgs, ", "))
			continue
		}
		if covered[v.Name] {
			fail(arm.clause.Case, "unreachable match arm: %s is already covered by the arms above", arm.pat.Root.String())
			continue
		}
		covered[v.Name] = true

		// Field patterns: binders and wildcards in v0.2.0 phase 5;
		// nested constructor patterns arrive with the GADT phase.
		if arm.pat.Root.HasArgs && len(arm.pat.Root.Args) != len(v.Params) {
			fail(arm.clause.Case, "pattern %s has %d fields but %s declares %d",
				arm.pat.Root.String(), len(arm.pat.Root.Args), v.Name, len(v.Params))
			continue
		}
		if !arm.pat.Root.HasArgs && len(v.Params) > 0 {
			fail(arm.clause.Case, "pattern %s must bind %d fields (or use %s(_%s))",
				v.Name, len(v.Params), v.Name, strings.Repeat(", _", len(v.Params)-1))
			continue
		}

		var bindings []string
		if arm.pat.Binder != "" {
			bindings = append(bindings, fmt.Sprintf("%s := %s", arm.pat.Binder, varName))
		}
		bodyText := r.armBodyText(sw, arm)
		for fi, argPat := range arm.pat.Root.Args {
			switch {
			case argPat.Wild:
			case argPat.HasArgs || argPat.Qual != "":
				fail(arm.clause.Case, "nested patterns are not implemented yet")
			default:
				if identReferencedInText(bodyText, argPat.Name) {
					bindings = append(bindings, fmt.Sprintf("%s := %s.%s", argPat.Name, varName, v.Params[fi].FieldName))
				}
			}
		}
		totalBindings += len(bindings)
		if arm.pat.Binder != "" && !identReferencedInText(bodyText, arm.pat.Binder) {
			// bound but unused would trip the compiler; drop it
			bindings = bindings[1:]
			totalBindings--
		}
		head, ok := r.caseTypeText(e, v, targTexts)
		if !ok {
			failed = true
			continue
		}
		plans = append(plans, armPlan{arm: arm, head: head, bindings: bindings})
	}

	// Exhaustiveness (flat patterns: per-variant coverage is exact).
	if !failed && !sawWildcard {
		var missing []string
		for _, v := range e.Variants {
			if possible[v.Name] && !covered[v.Name] {
				missing = append(missing, witness(v))
			}
		}
		if len(missing) > 0 {
			fail(matchPos, "non-exhaustive match on %s: missing %s; add the missing cases or a 'case _:' arm",
				r.localTypeString(tv.Type), strings.Join(missing, ", "))
		}
	}
	if failed {
		return
	}

	// Emit the resolution edits.
	for _, p := range plans {
		head := "default:"
		if p.head != "default" {
			head = "case " + p.head + ":"
		}
		r.edits = append(r.edits, lower.Edit{
			Start: r.off(p.arm.clause.Case),
			End:   r.off(p.arm.clause.Colon) + 1,
			New:   head,
		})
		repl := ""
		for _, b := range p.bindings {
			repl += b + "\n"
		}
		r.edits = append(r.edits, lower.Edit{Start: p.arm.carrier[0], End: p.arm.carrier[1], New: repl})
	}
	if !sawWildcard {
		rbrace := r.off(sw.Body.Rbrace)
		r.edits = append(r.edits, lower.Edit{
			Start: rbrace,
			End:   rbrace,
			New:   "default:\n\tpanic(\"gpp: impossible enum value in match\")\n",
		})
	}
	if totalBindings == 0 {
		// An unused type-switch guard variable is a compile error; drop
		// the assignment when nothing binds.
		assign := sw.Assign.(*ast.AssignStmt)
		r.edits = append(r.edits, lower.Edit{
			Start: r.off(assign.Lhs[0].Pos()),
			End:   r.off(assign.Rhs[0].Pos()),
			New:   "",
		})
	}
}

// skeletonGuard recognizes `switch __gpp_mN := any(subj).(type)`.
func skeletonGuard(sw *ast.TypeSwitchStmt) (varName string, subj ast.Expr, ok bool) {
	assign, isAssign := sw.Assign.(*ast.AssignStmt)
	if !isAssign || len(assign.Lhs) != 1 || len(assign.Rhs) != 1 {
		return "", nil, false
	}
	id, isIdent := assign.Lhs[0].(*ast.Ident)
	if !isIdent || !strings.HasPrefix(id.Name, "__gpp_m") {
		return "", nil, false
	}
	ta, isTA := assign.Rhs[0].(*ast.TypeAssertExpr)
	if !isTA {
		return "", nil, false
	}
	call, isCall := ta.X.(*ast.CallExpr)
	if !isCall || len(call.Args) != 1 {
		return "", nil, false
	}
	if fn, isID := call.Fun.(*ast.Ident); !isID || fn.Name != "any" {
		return "", nil, false
	}
	return id.Name, call.Args[0], true
}

// collectArms pairs each clause with its carrier line. allCarriers is
// false when any clause lacks one (already resolved).
func (r *fileResolver) collectArms(sw *ast.TypeSwitchStmt) ([]*matchArm, bool) {
	var arms []*matchArm
	clauses := sw.Body.List
	for i, stmt := range clauses {
		cc, ok := stmt.(*ast.CaseClause)
		if !ok {
			return nil, false
		}
		searchEnd := r.off(sw.Body.Rbrace)
		if i+1 < len(clauses) {
			searchEnd = r.off(clauses[i+1].Pos())
		}
		searchStart := r.off(cc.Colon)
		region := string(r.src[searchStart:searchEnd])
		idx := strings.Index(region, lower.PatternCarrier)
		if idx < 0 {
			return nil, false
		}
		lineStart := searchStart + idx
		lineEnd := lineStart
		for lineEnd < len(r.src) && r.src[lineEnd] != '\n' {
			lineEnd++
		}
		if lineEnd < len(r.src) {
			lineEnd++
		}
		patText := strings.TrimSpace(string(r.src[lineStart+len(lower.PatternCarrier) : lineEnd]))
		pat, err := syntax.ParsePatternText(patText)
		if err != nil {
			return nil, false
		}
		arms = append(arms, &matchArm{clause: cc, pat: pat, carrier: [2]int{lineStart, lineEnd}})
	}
	return arms, len(arms) > 0
}

// armVariant resolves an arm's constructor name against the enum.
func (r *fileResolver) armVariant(e *registry.Enum, arm *matchArm) (*registry.EnumVariant, string) {
	root := arm.pat.Root
	if root.Qual != "" {
		// Qualified: pkg.Variant or Enum.Variant — accept when the
		// qualifier plausibly names the enum's package or the enum.
		if root.Qual != e.Name {
			if alias, ok := r.importName(e.PkgPath); !ok || alias != root.Qual {
				return nil, fmt.Sprintf("pattern %s does not name a variant of %s", root.String(), e.Name)
			}
		}
	}
	if v, ok := e.Variant(root.Name); ok {
		return v, ""
	}
	// Also accept the lowered struct type name spelling.
	for _, v := range e.Variants {
		if v.TypeName == root.Name {
			return v, ""
		}
	}
	return nil, fmt.Sprintf("%s is not a variant of %s", root.Name, e.Name)
}

// caseTypeText renders the instantiated variant type for a case head.
func (r *fileResolver) caseTypeText(e *registry.Enum, v *registry.EnumVariant, targTexts []string) (string, bool) {
	name := v.TypeName
	if e.PkgPath != r.pkg.PkgPath {
		alias, ok := r.importName(e.PkgPath)
		if !ok {
			r.errorf(token.NoPos, "matching %s requires importing %q", e.Name, e.PkgPath)
			return "", false
		}
		name = alias + "." + name
	}
	kept := keptIndices(e, v)
	if len(kept) == 0 {
		return name, true
	}
	parts := make([]string, len(kept))
	for i, ki := range kept {
		parts[i] = targTexts[ki]
	}
	return name + "[" + strings.Join(parts, ", ") + "]", true
}

// variantPossible applies GADT filtering: can this variant inhabit the
// scrutinee's instantiation?
func (r *fileResolver) variantPossible(e *registry.Enum, v *registry.EnumVariant, targTypes []types.Type, targTexts []string) bool {
	if v.ResultArgs == nil {
		return true
	}
	for i, arg := range v.ResultArgs {
		if i >= len(e.TParams) || arg == e.TParams[i] {
			continue // kept position
		}
		// Ground position: the scrutinee's argument must be that type —
		// or a type parameter, which may be refined to it at runtime.
		if _, isTP := targTypes[i].(*types.TypeParam); isTP {
			continue
		}
		if targTexts[i] == arg {
			continue
		}
		if ground := r.evalInPkg(e.PkgPath, arg); ground != nil && types.Identical(ground, targTypes[i]) {
			continue
		}
		return false
	}
	return true
}

// localTypeString renders a type with package-local names.
func (r *fileResolver) localTypeString(t types.Type) string {
	return types.TypeString(t, types.RelativeTo(r.pkg.Types))
}

// evalInPkg evaluates a type expression in another package's scope.
func (r *fileResolver) evalInPkg(pkgPath, text string) types.Type {
	tp, ok := r.typesByPath[pkgPath]
	if !ok {
		return nil
	}
	tv, err := types.Eval(r.pkg.Fset, tp, token.NoPos, text)
	if err != nil || !tv.IsType() {
		return nil
	}
	return tv.Type
}

// witness renders the canonical missing-case pattern for a variant.
func witness(v *registry.EnumVariant) string {
	if len(v.Params) == 0 {
		return v.Name
	}
	return v.Name + "(_" + strings.Repeat(", _", len(v.Params)-1) + ")"
}

// armBodyText slices the source of an arm's body.
func (r *fileResolver) armBodyText(sw *ast.TypeSwitchStmt, arm *matchArm) string {
	end := r.off(sw.Body.Rbrace)
	if len(arm.clause.Body) > 0 {
		end = r.off(arm.clause.Body[len(arm.clause.Body)-1].End())
	}
	return string(r.src[arm.carrier[1]:end])
}

// identReferencedInText reports whether name occurs as a standalone
// identifier token in text (cheap word-boundary scan).
func identReferencedInText(text, name string) bool {
	for start := 0; ; {
		i := strings.Index(text[start:], name)
		if i < 0 {
			return false
		}
		i += start
		before := byte(' ')
		if i > 0 {
			before = text[i-1]
		}
		after := byte(' ')
		if i+len(name) < len(text) {
			after = text[i+len(name)]
		}
		if !isIdentByte(before) && !isIdentByte(after) {
			return true
		}
		start = i + len(name)
	}
}

func isIdentByte(b byte) bool {
	return b == '_' || (b >= 'a' && b <= 'z') || (b >= 'A' && b <= 'Z') || (b >= '0' && b <= '9')
}

// bareBreak finds a break statement (without label) at the arm's own
// nesting level — where its meaning would differ between lowering modes.
func bareBreak(stmts []ast.Stmt) token.Pos {
	for _, s := range stmts {
		if pos := bareBreakIn(s); pos != token.NoPos {
			return pos
		}
	}
	return token.NoPos
}

func bareBreakIn(s ast.Stmt) token.Pos {
	switch st := s.(type) {
	case *ast.BranchStmt:
		if st.Tok == token.BREAK && st.Label == nil {
			return st.Pos()
		}
	case *ast.BlockStmt:
		return bareBreak(st.List)
	case *ast.IfStmt:
		if pos := bareBreakIn(st.Body); pos != token.NoPos {
			return pos
		}
		if st.Else != nil {
			return bareBreakIn(st.Else)
		}
	case *ast.LabeledStmt:
		return bareBreakIn(st.Stmt)
		// for/range/switch/type-switch/select re-bind break: stop there.
	}
	return token.NoPos
}
