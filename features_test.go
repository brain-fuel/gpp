package goplus_test

import (
	"testing"

	"github.com/cucumber/godog"

	"goforge.dev/goplus/internal/bddtest"
)

// TestFeatures runs the Gherkin spec suite under features/ with Godog.
// The feature files plus spec/grammar-*.ebnf are the goplus specification.
func TestFeatures(t *testing.T) {
	suite := godog.TestSuite{
		Name: "goplus",
		ScenarioInitializer: func(sc *godog.ScenarioContext) {
			bddtest.InitializeScenario(t, sc)
		},
		Options: &godog.Options{
			Format:   "progress",
			Paths:    []string{"features"},
			Strict:   true,
			TestingT: t,
		},
	}
	if suite.Run() != 0 {
		t.Fatal("feature suite failed")
	}
}
