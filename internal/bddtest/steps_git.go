package bddtest

import (
	"fmt"
	"os/exec"
	"strings"

	"github.com/cucumber/godog"
)

func initGitSteps(sc *godog.ScenarioContext, w func() *World) {
	sc.Step(`^a git repository$`, func() error {
		world := w()
		for _, args := range [][]string{
			{"init", "-q"},
			{"config", "user.email", "spec@example.com"},
			{"config", "user.name", "gpp spec"},
			{"add", "-A"},
			{"commit", "-q", "-m", "fixture", "--allow-empty"},
		} {
			cmd := exec.Command("git", args...)
			cmd.Dir = world.Dir
			if out, err := cmd.CombinedOutput(); err != nil {
				return fmt.Errorf("git %v: %v\n%s", args, err, out)
			}
		}
		return nil
	})

	sc.Step(`^the git staging area contains "([^"]+)"$`, func(name string) error {
		world := w()
		cmd := exec.Command("git", "diff", "--cached", "--name-only")
		cmd.Dir = world.Dir
		out, err := cmd.CombinedOutput()
		if err != nil {
			return fmt.Errorf("git diff --cached: %v\n%s", err, out)
		}
		for _, line := range strings.Split(string(out), "\n") {
			if strings.TrimSpace(line) == name {
				return nil
			}
		}
		return fmt.Errorf("staging area does not contain %q; staged:\n%s", name, out)
	})
}
