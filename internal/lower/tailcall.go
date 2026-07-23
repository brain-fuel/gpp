package lower

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"strconv"
	"strings"
)

// TailPrefix marks a function declared with the Go+ `tail` modifier.
const TailPrefix = "//goplus:tail"

// TailError describes an invalid use of the recur tail-call intrinsic.
type TailError struct {
	Pos token.Position
	Msg string
}

// LowerTailCalls lowers explicit recur(nextArgs...) tail statements to a
// labelled loop. It runs after the other Go+ source rewrites, so recur works
// uniformly inside authored Go control flow and lowered constructs such as
// match.
func LowerTailCalls(filename string, src []byte) ([]byte, []TailError) {
	// Most Go+ files do not use tail recursion. Avoid feeding otherwise valid
	// Go+ syntax (notably nested dependent type applications) to go/parser
	// unless a declaration can actually require this lowering pass.
	if !bytes.Contains(src, []byte(TailPrefix)) && !bytes.Contains(src, []byte("//goplus:total ")) {
		return src, nil
	}
	fset := token.NewFileSet()
	// Keep parser object resolution here solely to distinguish the predeclared
	// panic from a shadowing user symbol in the fallthrough proof.
	file, err := parser.ParseFile(fset, filename, src, parser.ParseComments)
	if err != nil {
		message := fmt.Sprintf("internal error: tail-call input does not parse: %v", err)
		if errors, ok := err.(scanner.ErrorList); ok && len(errors) > 0 {
			lines := bytes.Split(src, []byte("\n"))
			line := errors[0].Pos.Line
			if line > 0 && line <= len(lines) {
				message += fmt.Sprintf("; rewritten line %d: %s", line, strings.TrimSpace(string(lines[line-1])))
			}
		}
		return src, []TailError{{Msg: message}}
	}
	var edits []Edit
	var errs []TailError
	visitFunc := func(typ *ast.FuncType, body *ast.BlockStmt, skipLoweredReceiver bool) {
		if body == nil {
			return
		}

		allowed := map[*ast.CallExpr]bool{}
		markTailBlock(body, allowed)
		var calls []*ast.CallExpr
		ast.Inspect(body, func(n ast.Node) bool {
			if _, ok := n.(*ast.FuncLit); ok {
				return false
			}
			call, ok := n.(*ast.CallExpr)
			if ok && isRecurCall(call) {
				calls = append(calls, call)
			}
			return true
		})
		if len(calls) == 0 {
			return
		}
		if typ.Results != nil && len(typ.Results.List) > 0 && !tailBlockTerminates(body, allowed) {
			errs = append(errs, TailError{
				Pos: fset.Position(body.Rbrace),
				Msg: "function using recur can fall through without returning",
			})
			return
		}
		params, paramErr := tailParamNames(typ.Params, skipLoweredReceiver)
		label := freshTailLabel(body)
		valid := true
		for _, call := range calls {
			bad := func(format string, args ...any) {
				errs = append(errs, TailError{Pos: fset.Position(call.Pos()), Msg: fmt.Sprintf(format, args...)})
				valid = false
			}
			if !allowed[call] {
				bad("recur must be a final statement of the function or a tail branch")
				continue
			}
			if paramErr != "" {
				bad("recur requires every function parameter to have a name: %s", paramErr)
				continue
			}
			if call.Ellipsis.IsValid() {
				bad("recur arguments are parameter values, so ... is not permitted")
				continue
			}
			if len(call.Args) != len(params) {
				bad("recur has %d arguments, want %d function parameters", len(call.Args), len(params))
				continue
			}
			replacement := "continue " + label
			if len(params) > 0 {
				args := make([]string, len(call.Args))
				for i, arg := range call.Args {
					args[i] = sourceText(src, fset, arg.Pos(), arg.End())
				}
				replacement = "{ " + strings.Join(params, ", ") + " = " + strings.Join(args, ", ") + "; continue " + label + " }"
			}
			edits = append(edits, Edit{Start: offset(fset, call.Pos()), End: offset(fset, call.End()), New: replacement})
		}
		if !valid {
			return
		}
		loopEnd := "\n}\n"
		if typ.Results == nil || len(typ.Results.List) == 0 {
			// Preserve ordinary fallthrough for a result-less function.
			loopEnd = "\nbreak\n}\n"
		}
		edits = append(edits,
			Edit{Start: offset(fset, body.Lbrace) + 1, End: offset(fset, body.Lbrace) + 1, New: "\n" + label + ":\nfor {"},
			Edit{Start: offset(fset, body.Rbrace), End: offset(fset, body.Rbrace), New: loopEnd},
		)
	}

	for _, decl := range file.Decls {
		if fd, ok := decl.(*ast.FuncDecl); ok {
			enabled, sourceReceiver := tailEnabled(fd)
			if enabled {
				visitFunc(fd.Type, fd.Body, fd.Recv == nil && sourceReceiver != "")
			}
		}
	}
	if len(errs) > 0 || len(edits) == 0 {
		return src, errs
	}
	out, err := Apply(src, edits)
	if err != nil {
		return src, []TailError{{Msg: err.Error()}}
	}
	return out, nil
}

func tailEnabled(fd *ast.FuncDecl) (enabled bool, sourceReceiver string) {
	if fd.Doc == nil {
		return false, ""
	}
	for _, comment := range fd.Doc.List {
		if comment.Text == TailPrefix {
			return true, ""
		}
		if rest, ok := strings.CutPrefix(comment.Text, TailPrefix+" receiver="); ok {
			return true, strings.TrimSpace(rest)
		}
		if strings.HasPrefix(comment.Text, "//goplus:total ") {
			return true, ""
		}
	}
	return false, ""
}

// tailBlockTerminates is the small control-flow proof needed before an
// infinite lowering loop is introduced around a result-bearing function.
// It intentionally accepts only forms whose termination is syntactically
// evident; this prevents recur from turning an ordinary missing-return error
// into an accidental infinite loop.
func tailBlockTerminates(block *ast.BlockStmt, allowed map[*ast.CallExpr]bool) bool {
	if block == nil {
		return false
	}
	for _, stmt := range block.List {
		if tailStmtTerminates(stmt, allowed) {
			return true
		}
	}
	return false
}

func tailStmtTerminates(stmt ast.Stmt, allowed map[*ast.CallExpr]bool) bool {
	switch s := stmt.(type) {
	case *ast.ReturnStmt:
		return true
	case *ast.ExprStmt:
		if call, ok := s.X.(*ast.CallExpr); ok {
			if allowed[call] {
				return true
			}
			if id, ok := call.Fun.(*ast.Ident); ok && id.Name == "panic" && id.Obj == nil {
				return true
			}
		}
	case *ast.BlockStmt:
		return tailBlockTerminates(s, allowed)
	case *ast.LabeledStmt:
		return tailStmtTerminates(s.Stmt, allowed)
	case *ast.IfStmt:
		return s.Else != nil && tailBlockTerminates(s.Body, allowed) && tailStmtTerminates(s.Else, allowed)
	case *ast.ForStmt:
		return s.Cond == nil && !containsBreak(s.Body)
	case *ast.SwitchStmt:
		return terminatingClauses(s.Body.List, allowed, true)
	case *ast.TypeSwitchStmt:
		return terminatingClauses(s.Body.List, allowed, !isMatchSkeleton(s))
	case *ast.SelectStmt:
		// select{} and a select whose every case terminates cannot fall through.
		return len(s.Body.List) == 0 || terminatingClauses(s.Body.List, allowed, false)
	}
	return false
}

func isMatchSkeleton(sw *ast.TypeSwitchStmt) bool {
	assign, ok := sw.Assign.(*ast.AssignStmt)
	if !ok || len(assign.Lhs) != 1 || len(assign.Rhs) != 1 {
		return false
	}
	id, ok := assign.Lhs[0].(*ast.Ident)
	if !ok || !strings.HasPrefix(id.Name, "__gp_m") {
		return false
	}
	assertion, ok := assign.Rhs[0].(*ast.TypeAssertExpr)
	if !ok || assertion.Type != nil {
		return false
	}
	call, ok := assertion.X.(*ast.CallExpr)
	if !ok || len(call.Args) != 1 {
		return false
	}
	fun, ok := call.Fun.(*ast.Ident)
	return ok && fun.Name == "any"
}

func terminatingClauses(stmts []ast.Stmt, allowed map[*ast.CallExpr]bool, requireDefault bool) bool {
	if len(stmts) == 0 {
		return false
	}
	hasDefault := false
	for _, stmt := range stmts {
		var body []ast.Stmt
		var isDefault bool
		switch clause := stmt.(type) {
		case *ast.CaseClause:
			body, isDefault = clause.Body, clause.List == nil
		case *ast.CommClause:
			body, isDefault = clause.Body, clause.Comm == nil
		default:
			return false
		}
		if isDefault {
			hasDefault = true
		}
		if !tailBlockTerminates(&ast.BlockStmt{List: body}, allowed) {
			return false
		}
	}
	return !requireDefault || hasDefault
}

func containsBreak(body *ast.BlockStmt) bool {
	found := false
	ast.Inspect(body, func(n ast.Node) bool {
		if found {
			return false
		}
		switch x := n.(type) {
		case *ast.FuncLit:
			return false
		case *ast.BranchStmt:
			if x.Tok == token.BREAK {
				found = true
				return false
			}
		}
		return true
	})
	return found
}

func isRecurCall(call *ast.CallExpr) bool {
	id, ok := call.Fun.(*ast.Ident)
	return ok && id.Name == "recur"
}

func markTailBlock(block *ast.BlockStmt, allowed map[*ast.CallExpr]bool) {
	if block != nil && len(block.List) > 0 {
		markTailStmt(block.List[len(block.List)-1], allowed)
	}
}

func markTailStmt(stmt ast.Stmt, allowed map[*ast.CallExpr]bool) {
	switch s := stmt.(type) {
	case *ast.ExprStmt:
		if call, ok := s.X.(*ast.CallExpr); ok && isRecurCall(call) {
			allowed[call] = true
		}
	case *ast.BlockStmt:
		markTailBlock(s, allowed)
	case *ast.LabeledStmt:
		markTailStmt(s.Stmt, allowed)
	case *ast.IfStmt:
		markTailBlock(s.Body, allowed)
		if s.Else != nil {
			markTailStmt(s.Else, allowed)
		}
	case *ast.SwitchStmt:
		markTailClauses(s.Body.List, allowed)
	case *ast.TypeSwitchStmt:
		markTailClauses(s.Body.List, allowed)
	case *ast.SelectStmt:
		markTailClauses(s.Body.List, allowed)
	}
}

func markTailClauses(stmts []ast.Stmt, allowed map[*ast.CallExpr]bool) {
	for _, stmt := range stmts {
		var body []ast.Stmt
		switch clause := stmt.(type) {
		case *ast.CaseClause:
			body = clause.Body
		case *ast.CommClause:
			body = clause.Body
		}
		if len(body) == 0 {
			continue
		}
		markTailStmt(body[len(body)-1], allowed)
	}
}

func tailParamNames(fields *ast.FieldList, skipFirst bool) ([]string, string) {
	if fields == nil {
		return nil, ""
	}
	var names []string
	seen := 0
	for _, field := range fields.List {
		if len(field.Names) == 0 {
			return nil, "an unnamed parameter cannot be rebound"
		}
		for _, name := range field.Names {
			if skipFirst && seen == 0 {
				seen++
				continue
			}
			seen++
			if name.Name == "_" {
				return nil, "the blank parameter cannot be rebound"
			}
			names = append(names, name.Name)
		}
	}
	return names, ""
}

func freshTailLabel(body *ast.BlockStmt) string {
	used := map[string]bool{}
	ast.Inspect(body, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			used[id.Name] = true
		}
		return true
	})
	base := "__goplus_recur"
	for i := 0; ; i++ {
		name := base
		if i > 0 {
			name += strconv.Itoa(i)
		}
		if !used[name] {
			return name
		}
	}
}

func offset(fset *token.FileSet, pos token.Pos) int { return fset.Position(pos).Offset }

func sourceText(src []byte, fset *token.FileSet, start, end token.Pos) string {
	return string(src[offset(fset, start):offset(fset, end)])
}
