package resolve

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"strings"

	"goforge.dev/gpp/internal/lower"
	"goforge.dev/gpp/internal/registry"
	"goforge.dev/gpp/internal/syntax"
)

// Match resolution. Pass 1 lowers every match to a type switch whose case
// heads are `case nil:` placeholders followed by `//gpp:pattern` carrier
// comments. Once the scrutinee's type is known, one pass resolves the
// whole match. Flat matches stay type switches (idiomatic output); a match
// with nested patterns is regenerated as a goto chain — type switches
// cannot fall through on a failed nested check, and two arms may share a
// head constructor. Exhaustiveness and reachability run on Maranget
// usefulness over the GADT-filtered universe; GADT-refined arms wrap
// T-typed returns in any(x).(T).

// armAnalysis is one fully analyzed arm.
type armAnalysis struct {
	clause     *ast.CaseClause
	carrier    [2]int
	pat        *rpat
	alts       []*rpat // additional alternatives of a multi-pattern arm (v0.12.0)
	binderName string
	body       string // verbatim body text (chain mode)
	nested     bool
	refined    map[string]string // scrutinee tparam name -> ground type text
}

// matchCandidate inspects a type switch produced by lower.MatchSkeleton.
func (r *fileResolver) matchCandidate(sw *ast.TypeSwitchStmt) {
	varName, subj, ok := skeletonGuard(sw)
	if !ok {
		return
	}
	rawArms, allCarriers := r.collectArms(sw)
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
	tparamNames := map[string]bool{}
	for _, t := range targTypes {
		if tp, isTP := t.(*types.TypeParam); isTP {
			tparamNames[tp.Obj().Name()] = true
		}
	}
	idxTerms := r.scrutineeIndexTerms(e, subj)
	rootCol := patCol{enum: e, targs: targTexts, idxTerms: idxTerms, pos: subj.Pos()}

	possible := map[string]bool{}
	idxOut := map[string]bool{}
	for _, v := range e.Variants {
		possible[v.Name] = r.variantPossible(e, v, targTypes, targTexts)
		if possible[v.Name] && indexRulesOut(r.reg, rootCol, v) {
			possible[v.Name] = false
			idxOut[v.Name] = true
		}
	}

	failed := false
	fail := func(pos token.Pos, format string, args ...any) {
		r.errorf(pos, format, args...)
		failed = true
	}

	// Analyze arms.
	var arms []*armAnalysis
	sawWildcard := false
	anyNested := false
	for i, raw := range rawArms {
		if sawWildcard {
			fail(raw.clause.Case, "'case _:' must be the last arm of a match")
			break
		}
		if bad := bareBreak(raw.clause.Body); bad != token.NoPos {
			fail(bad, "break is not supported directly inside a match arm in v0.2.0; label the enclosing loop")
		}
		a := &armAnalysis{clause: raw.clause, carrier: raw.carrier, binderName: raw.pat.Binder}
		a.body = r.armBodyText(sw, raw)
		if raw.pat.Root.Wild {
			sawWildcard = true
			if i != len(rawArms)-1 {
				fail(raw.clause.Case, "'case _:' must be the last arm of a match")
			}
			a.pat = &rpat{wild: true, col: rootCol}
			arms = append(arms, a)
			continue
		}
		rp, errMsg := r.resolveRPat(raw.pat.Root, rootCol, true, tparamNames)
		if errMsg != "" {
			fail(raw.clause.Case, "%s", errMsg)
			continue
		}
		a.pat = rp
		// Multi-pattern arm (v0.12.0): every pattern is flat — a
		// constructor whose arguments are all wildcards (the arm body
		// cannot know which alternative matched, so nothing can bind).
		if len(raw.pat.Alts) > 0 {
			if a.binderName != "" {
				fail(raw.clause.Case, "a multi-pattern arm cannot bind the value (the alternatives have different types); bind by splitting the arm")
				continue
			}
			if !flatWildOnly(raw.pat.Root) {
				fail(raw.clause.Case, "patterns in a multi-pattern arm take only wildcard arguments; bind by splitting the arm")
				continue
			}
			altsOK := true
			for _, altNode := range raw.pat.Alts {
				if !flatWildOnly(altNode) {
					fail(raw.clause.Case, "patterns in a multi-pattern arm take only wildcard arguments; bind by splitting the arm")
					altsOK = false
					break
				}
				arp, altErr := r.resolveRPat(altNode, rootCol, true, tparamNames)
				if altErr != "" {
					fail(raw.clause.Case, "%s", altErr)
					altsOK = false
					break
				}
				if !possible[arp.variant.Name] {
					fail(raw.clause.Case, "pattern %s can never match a value of type %s",
						altNode.String(), r.localTypeString(tv.Type))
					altsOK = false
					break
				}
				a.alts = append(a.alts, arp)
			}
			if !altsOK {
				continue
			}
		}
		if !possible[rp.variant.Name] {
			if idxOut[rp.variant.Name] {
				fail(raw.clause.Case, "pattern %s can never match: the scrutinee's index (%s) rules out %s (its index is %s)",
					raw.pat.Root.String(), strings.Join(idxTerms, ", "), rp.variant.Name, strings.Join(rp.variant.IndexArgs, ", "))
			} else {
				fail(raw.clause.Case, "pattern %s can never match a value of type %s: %s constructs %s[%s]",
					raw.pat.Root.String(), r.localTypeString(tv.Type), rp.variant.Name, e.Name, strings.Join(rp.variant.ResultArgs, ", "))
			}
			continue
		}
		if patNested(rp) {
			a.nested = true
			anyNested = true
		}
		a.refined = r.refinements(e, rp.variant, targTypes)
		arms = append(arms, a)
	}
	if failed {
		return
	}

	// Usefulness: reachability per arm, then exhaustiveness.
	u := &usefulCtx{r: r, tparamNames: tparamNames}
	cols := []patCol{rootCol}
	var rows [][]syntax.PatNode
	for _, a := range arms {
		for _, rp := range append([]*rpat{a.pat}, a.alts...) {
			row := []syntax.PatNode{normPat(rp)}
			if ok, _ := u.useful(cols, rows, row); !ok && !u.overflow {
				fail(a.clause.Case, "unreachable match arm: %s is already covered by the arms above", renderWitness(row))
			}
			rows = append(rows, row)
		}
	}
	if !failed {
		if ok, w := u.useful(cols, rows, []syntax.PatNode{{Wild: true}}); ok {
			fail(sw.Pos(), "non-exhaustive match on %s: missing %s; add the missing cases or a 'case _:' arm",
				r.localTypeString(tv.Type), renderWitness(w))
		}
	}
	if u.overflow {
		fail(sw.Pos(), "match is too complex to check exhaustively; add a 'case _:' arm")
	}
	if failed {
		return
	}

	// Refinement: leave a //gpp:refine carrier at the top of each refined
	// arm; a later fixpoint iteration applies type-directed wraps at every
	// mismatched conversion boundary (refine.go), once the arm's bindings
	// have made its body typable.
	for _, a := range arms {
		if len(a.refined) == 0 {
			continue
		}
		if anyNested {
			a.body = refineCarrierLine(a.refined) + "\n" + a.body
		}
	}

	subjText := r.text(subj.Pos(), subj.End())
	if anyNested {
		for _, a := range arms {
			if len(a.alts) > 0 {
				fail(a.clause.Case, "a multi-pattern arm cannot share a match with nested patterns; split the arm")
			}
		}
		if failed {
			return
		}
		r.edits = append(r.edits, lower.Edit{
			Start: r.off(sw.Pos()),
			End:   r.off(sw.End()),
			New:   r.chainEmit(sw, varName, subjText, arms, sawWildcard),
		})
		return
	}

	// Flat: in-place type-switch resolution.
	totalBindings := 0
	type armPlan struct {
		arm      *armAnalysis
		head     string
		bindings []string
	}
	var plans []armPlan
	for _, a := range arms {
		if a.pat.wild {
			plans = append(plans, armPlan{arm: a, head: "default"})
			continue
		}
		var bindings []string
		if a.binderName != "" && identReferencedInText(a.body, a.binderName) {
			bindings = append(bindings, fmt.Sprintf("%s := %s", a.binderName, varName))
		}
		for fi, argPat := range a.pat.args {
			if argPat.binder != "" && identReferencedInText(a.body, argPat.binder) {
				bindings = append(bindings, fmt.Sprintf("%s := %s.%s", argPat.binder, varName, a.pat.variant.Params[fi].FieldName))
			}
		}
		totalBindings += len(bindings)
		head, headOK := r.rpatCaseType(a.pat, a.clause.Case)
		if !headOK {
			return
		}
		for _, alt := range a.alts {
			altHead, altOK := r.rpatCaseType(alt, a.clause.Case)
			if !altOK {
				return
			}
			head += ", " + altHead
		}
		plans = append(plans, armPlan{arm: a, head: head, bindings: bindings})
	}

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
		if len(p.arm.refined) > 0 {
			repl += refineCarrierLine(p.arm.refined) + "\n"
		}
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

// flatWildOnly reports whether a pattern is a constructor whose arguments
// are all wildcards (the multi-pattern arm shape).
func flatWildOnly(n syntax.PatNode) bool {
	for _, a := range n.Args {
		if !a.Wild {
			return false
		}
	}
	return true
}

// patNested reports whether any argument is itself a constructor pattern.
func patNested(p *rpat) bool {
	for _, a := range p.args {
		if a.variant != nil {
			return true
		}
	}
	return false
}

// refinements computes scrutinee-tparam refinements a variant implies,
// structurally: wherever a scrutinee-side type parameter aligns with a
// GROUND subterm of the variant's result-arg pattern, the parameter
// refines to that subterm's text.
func (r *fileResolver) refinements(e *registry.Enum, v *registry.EnumVariant, targTypes []types.Type) map[string]string {
	if v.ResultArgs == nil {
		return nil
	}
	tset := map[string]bool{}
	for _, n := range e.TParams {
		tset[n] = true
	}
	out := map[string]string{}
	for i, arg := range v.ResultArgs {
		if i >= len(targTypes) {
			continue
		}
		pat, err := parser.ParseExpr(arg)
		if err != nil {
			continue
		}
		r.refineFromPat(pat, targTypes[i], tset, out)
	}
	if len(out) == 0 {
		return nil
	}
	return out
}

// refineFromPat walks a pattern against a scrutinee type, recording
// refinements where a scrutinee type parameter aligns with a ground
// pattern subterm.
func (r *fileResolver) refineFromPat(pat ast.Expr, actual types.Type, tset map[string]bool, out map[string]string) {
	if tp, isTP := types.Unalias(actual).(*types.TypeParam); isTP {
		text := exprText(pat)
		if !textHasTParam(text, tset) {
			out[tp.Obj().Name()] = text
		}
		return
	}
	switch p := pat.(type) {
	case *ast.StarExpr:
		if a, ok := types.Unalias(actual).(*types.Pointer); ok {
			r.refineFromPat(p.X, a.Elem(), tset, out)
		}
	case *ast.ArrayType:
		switch a := types.Unalias(actual).(type) {
		case *types.Slice:
			if p.Len == nil {
				r.refineFromPat(p.Elt, a.Elem(), tset, out)
			}
		case *types.Array:
			if p.Len != nil {
				r.refineFromPat(p.Elt, a.Elem(), tset, out)
			}
		}
	case *ast.MapType:
		if a, ok := types.Unalias(actual).(*types.Map); ok {
			r.refineFromPat(p.Key, a.Key(), tset, out)
			r.refineFromPat(p.Value, a.Elem(), tset, out)
		}
	case *ast.ChanType:
		if a, ok := types.Unalias(actual).(*types.Chan); ok {
			r.refineFromPat(p.Value, a.Elem(), tset, out)
		}
	case *ast.IndexExpr:
		if a, ok := types.Unalias(actual).(*types.Named); ok && a.TypeArgs() != nil && a.TypeArgs().Len() == 1 {
			r.refineFromPat(p.Index, a.TypeArgs().At(0), tset, out)
		}
	case *ast.IndexListExpr:
		if a, ok := types.Unalias(actual).(*types.Named); ok && a.TypeArgs() != nil && a.TypeArgs().Len() == len(p.Indices) {
			for i, idx := range p.Indices {
				r.refineFromPat(idx, a.TypeArgs().At(i), tset, out)
			}
		}
	}
}

// matchArm is one clause of a skeleton match, textually collected.
type matchArm struct {
	clause  *ast.CaseClause
	pat     syntax.PatText
	carrier [2]int // byte range of the carrier line (incl. newline)
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

// localTypeString renders a type with package-local names.
func (r *fileResolver) localTypeString(t types.Type) string {
	return types.TypeString(t, types.RelativeTo(r.pkg.Types))
}

// variantPossible applies GADT filtering: can this variant inhabit the
// scrutinee's instantiation? Structural under v0.6.0: each result-arg
// pattern must be lax-compatible with the scrutinee's argument (pattern
// tparams and scrutinee type parameters match anything; ground leaves
// compare by identity in the enum's package).
func (r *fileResolver) variantPossible(e *registry.Enum, v *registry.EnumVariant, targTypes []types.Type, targTexts []string) bool {
	if v.ResultArgs == nil {
		return true
	}
	patWild := map[string]bool{}
	for _, n := range e.TParams {
		patWild[n] = true
	}
	groundEq := func(a, b string) bool {
		ga := r.evalInPkg(e.PkgPath, a)
		gb := r.evalInPkg(e.PkgPath, b)
		return ga != nil && gb != nil && types.Identical(ga, gb)
	}
	argWild := map[string]bool{}
	for _, t := range targTypes {
		collectTypeParams(t, argWild)
	}
	for i, arg := range v.ResultArgs {
		if i >= len(targTypes) {
			return false
		}
		if _, isTP := targTypes[i].(*types.TypeParam); isTP {
			continue // refinable (or unmatchable) at this position
		}
		if !laxCompatible(arg, targTexts[i], patWild, argWild, groundEq) {
			return false
		}
	}
	return true
}

// collectTypeParams gathers type-parameter names occurring anywhere in a
// type.
func collectTypeParams(t types.Type, out map[string]bool) {
	switch x := types.Unalias(t).(type) {
	case *types.TypeParam:
		out[x.Obj().Name()] = true
	case *types.Pointer:
		collectTypeParams(x.Elem(), out)
	case *types.Slice:
		collectTypeParams(x.Elem(), out)
	case *types.Array:
		collectTypeParams(x.Elem(), out)
	case *types.Map:
		collectTypeParams(x.Key(), out)
		collectTypeParams(x.Elem(), out)
	case *types.Chan:
		collectTypeParams(x.Elem(), out)
	case *types.Signature:
		for i := 0; i < x.Params().Len(); i++ {
			collectTypeParams(x.Params().At(i).Type(), out)
		}
		for i := 0; i < x.Results().Len(); i++ {
			collectTypeParams(x.Results().At(i).Type(), out)
		}
	case *types.Named:
		if ta := x.TypeArgs(); ta != nil {
			for i := 0; i < ta.Len(); i++ {
				collectTypeParams(ta.At(i), out)
			}
		}
	}
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
