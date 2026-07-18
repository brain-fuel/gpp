package bddtest

// Step definitions for the v0.3.0 flow frontend: pipelines and
// composition. Renderers slice original source bytes, so assertions double
// as position-fidelity checks.

import (
	"fmt"
	"strings"

	"github.com/cucumber/godog"
)

func initParsingV3Steps(sc *godog.ScenarioContext, ps *parseState) {
	sc.Step(`^parsing succeeds with (\d+) pipelines?$`, func(want int) error {
		if ps.err != nil {
			return fmt.Errorf("parsing failed: %v", ps.err)
		}
		if got := len(ps.file.Pipes); got != want {
			return fmt.Errorf("found %d pipelines, want %d", got, want)
		}
		return nil
	})

	sc.Step(`^parsing succeeds with (\d+) compositions?$`, func(want int) error {
		if ps.err != nil {
			return fmt.Errorf("parsing failed: %v", ps.err)
		}
		if got := len(ps.file.Composes); got != want {
			return fmt.Errorf("found %d compositions, want %d", got, want)
		}
		return nil
	})

	sc.Step(`^pipeline (\d+) has head "([^"]*)" and stages "([^"]*)"$`, func(idx int, wantHead, wantStages string) error {
		if ps.err != nil {
			return fmt.Errorf("parsing failed: %v", ps.err)
		}
		if idx < 1 || idx > len(ps.file.Pipes) {
			return fmt.Errorf("no pipeline %d (have %d)", idx, len(ps.file.Pipes))
		}
		p := ps.file.Pipes[idx-1]
		head := srcText(ps.file, p.Head.Pos(), p.Head.End())
		var stages []string
		for _, st := range p.Stages {
			text := srcText(ps.file, st.Expr.Pos(), st.Expr.End())
			if st.Dot.IsValid() {
				text = "." + text
			}
			stages = append(stages, text)
		}
		got := strings.Join(stages, " | ")
		if head != wantHead || got != wantStages {
			return fmt.Errorf("pipeline %d: head %q stages %q, want head %q stages %q",
				idx, head, got, wantHead, wantStages)
		}
		return nil
	})

	sc.Step(`^composition (\d+) has operands "([^"]*)"$`, func(idx int, want string) error {
		if ps.err != nil {
			return fmt.Errorf("parsing failed: %v", ps.err)
		}
		if idx < 1 || idx > len(ps.file.Composes) {
			return fmt.Errorf("no composition %d (have %d)", idx, len(ps.file.Composes))
		}
		c := ps.file.Composes[idx-1]
		var ops []string
		for _, op := range c.Fns {
			ops = append(ops, srcText(ps.file, op.Pos(), op.End()))
		}
		got := strings.Join(ops, " | ")
		if got != want {
			return fmt.Errorf("composition %d operands %q, want %q", idx, got, want)
		}
		return nil
	})
}
