package bddtest

// Step definitions for the v0.4.0 typed-failure frontend.

import (
	"fmt"

	"github.com/cucumber/godog"
)

func initParsingV4Steps(sc *godog.ScenarioContext, ps *parseState) {
	count := func(kind string) func(int) error {
		return func(want int) error {
			if ps.err != nil {
				return fmt.Errorf("parsing failed: %v", ps.err)
			}
			var got int
			switch kind {
			case "try":
				got = len(ps.file.Tries)
			case "if":
				got = len(ps.file.IfExprs)
			case "switch":
				got = len(ps.file.SwitchExprs)
			case "match":
				got = len(ps.file.MatchExprs)
			}
			if got != want {
				return fmt.Errorf("found %d %s expressions, want %d", got, kind, want)
			}
			return nil
		}
	}
	sc.Step(`^parsing succeeds with (\d+) try suffix(?:es)?$`, count("try"))
	sc.Step(`^parsing succeeds with (\d+) if expressions?$`, count("if"))
	sc.Step(`^parsing succeeds with (\d+) switch expressions?$`, count("switch"))
	sc.Step(`^parsing succeeds with (\d+) match expressions?$`, count("match"))
}
