package bddtest

// Step definitions for the v0.2.0 frontend: enum declarations and match
// statements. Renderers slice original source bytes via File.Offset, so
// every assertion doubles as a position-fidelity check.

import (
	"fmt"
	"go/token"
	"strings"

	"github.com/cucumber/godog"

	"goforge.dev/goplus/internal/syntax"
)

func initParsingV2Steps(sc *godog.ScenarioContext, ps *parseState) {
	sc.Step(`^parsing succeeds with (\d+) enums?$`, func(want int) error {
		if ps.err != nil {
			return fmt.Errorf("parsing failed: %v", ps.err)
		}
		if got := len(ps.file.Enums); got != want {
			return fmt.Errorf("found %d enums, want %d", got, want)
		}
		return nil
	})

	sc.Step(`^enum (\d+) is "([^"]*)"$`, func(idx int, want string) error {
		e, err := enumAt(ps, idx)
		if err != nil {
			return err
		}
		if got := renderEnum(ps.file, e); got != want {
			return fmt.Errorf("enum %d is %q, want %q", idx, got, want)
		}
		return nil
	})

	sc.Step(`^enum (\d+) variant "([^"]+)" has result type "([^"]*)"$`, func(idx int, name, want string) error {
		v, err := variantNamed(ps, idx, name)
		if err != nil {
			return err
		}
		got := ""
		if v.Result != nil {
			got = srcText(ps.file, v.Result.Pos(), v.Result.End())
		}
		if got != want {
			return fmt.Errorf("variant %s result type = %q, want %q", name, got, want)
		}
		return nil
	})

	sc.Step(`^parsing succeeds with (\d+) match statements?$`, func(want int) error {
		if ps.err != nil {
			return fmt.Errorf("parsing failed: %v", ps.err)
		}
		if got := len(ps.file.Matches); got != want {
			return fmt.Errorf("found %d match statements, want %d", got, want)
		}
		return nil
	})

	sc.Step(`^match (\d+) has subject "([^"]*)"$`, func(idx int, want string) error {
		m, err := matchStmtAt(ps, idx)
		if err != nil {
			return err
		}
		if got := srcText(ps.file, m.Subject.Pos(), m.Subject.End()); got != want {
			return fmt.Errorf("match %d subject = %q, want %q", idx, got, want)
		}
		return nil
	})

	sc.Step(`^match (\d+) case (\d+) is "([^"]*)"$`, func(mi, ci int, want string) error {
		m, err := matchStmtAt(ps, mi)
		if err != nil {
			return err
		}
		if ci < 1 || ci > len(m.Cases) {
			return fmt.Errorf("no case %d (have %d)", ci, len(m.Cases))
		}
		if got := renderCase(ps.file, m.Cases[ci-1]); got != want {
			return fmt.Errorf("match %d case %d is %q, want %q", mi, ci, got, want)
		}
		return nil
	})
}

func enumAt(ps *parseState, idx int) (*syntax.EnumDecl, error) {
	if ps.err != nil {
		return nil, fmt.Errorf("parsing failed: %v", ps.err)
	}
	if idx < 1 || idx > len(ps.file.Enums) {
		return nil, fmt.Errorf("no enum %d (have %d)", idx, len(ps.file.Enums))
	}
	return ps.file.Enums[idx-1], nil
}

func variantNamed(ps *parseState, idx int, name string) (*syntax.Variant, error) {
	e, err := enumAt(ps, idx)
	if err != nil {
		return nil, err
	}
	for _, v := range e.Variants {
		if v.Name.Name == name {
			return v, nil
		}
	}
	return nil, fmt.Errorf("enum %d has no variant %q", idx, name)
}

func matchStmtAt(ps *parseState, idx int) (*syntax.MatchStmt, error) {
	if ps.err != nil {
		return nil, fmt.Errorf("parsing failed: %v", ps.err)
	}
	if idx < 1 || idx > len(ps.file.Matches) {
		return nil, fmt.Errorf("no match %d (have %d)", idx, len(ps.file.Matches))
	}
	return ps.file.Matches[idx-1], nil
}

// srcText slices original source bytes between two positions.
func srcText(f *syntax.File, from, to token.Pos) string {
	return string(f.Src[f.Offset(from):f.Offset(to)])
}

// renderEnum renders "Option[T]: Some(value T) | None".
func renderEnum(f *syntax.File, e *syntax.EnumDecl) string {
	var b strings.Builder
	b.WriteString(e.Spec.Name.Name)
	if tp := e.Spec.TypeParams; tp != nil {
		var names []string
		for _, field := range tp.List {
			for _, n := range field.Names {
				names = append(names, n.Name)
			}
		}
		b.WriteString("[" + strings.Join(names, ", ") + "]")
	}
	b.WriteString(": ")
	var parts []string
	for _, v := range e.Variants {
		parts = append(parts, renderVariant(f, v))
	}
	b.WriteString(strings.Join(parts, " | "))
	return b.String()
}

func renderVariant(f *syntax.File, v *syntax.Variant) string {
	out := v.Name.Name
	if v.Params != nil {
		var fields []string
		for _, field := range v.Params.List {
			var names []string
			for _, n := range field.Names {
				names = append(names, n.Name)
			}
			text := strings.Join(names, ", ")
			if len(names) > 0 {
				text += " "
			}
			text += string(f.Src[f.Offset(field.Type.Pos()):f.Offset(field.Type.End())])
			fields = append(fields, text)
		}
		out += "(" + strings.Join(fields, ", ") + ")"
	}
	return out
}

// renderCase renders "c := Circle(r)", "Add(Lit(a), _)", or "_".
func renderCase(f *syntax.File, c *syntax.CaseClause) string {
	out := renderPattern(f, c.Pattern)
	if c.Binder != nil {
		out = c.Binder.Name + " := " + out
	}
	return out
}

func renderPattern(f *syntax.File, p syntax.Pattern) string {
	switch pat := p.(type) {
	case *syntax.WildcardPattern:
		return "_"
	case *syntax.ConstructorPattern:
		out := string(f.Src[f.Offset(pat.Name.Pos()):f.Offset(pat.Name.End())])
		if pat.Lparen.IsValid() {
			var args []string
			for _, a := range pat.Args {
				args = append(args, renderPattern(f, a))
			}
			out += "(" + strings.Join(args, ", ") + ")"
		}
		return out
	}
	return "?"
}
