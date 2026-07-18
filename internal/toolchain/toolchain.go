// Package toolchain delegates to the standard go tool.
package toolchain

import (
	"io"
	"os"
	"os/exec"
)

// Go runs `go <sub> <args...>` in dir, wiring through stdio, and returns
// the exit code.
func Go(dir, sub string, args []string, stdout, stderr io.Writer) int {
	cmd := exec.Command("go", append([]string{sub}, args...)...)
	cmd.Dir = dir
	cmd.Stdin = os.Stdin
	cmd.Stdout = stdout
	cmd.Stderr = stderr
	if err := cmd.Run(); err != nil {
		if exit, ok := err.(*exec.ExitError); ok {
			return exit.ExitCode()
		}
		return 1
	}
	return 0
}
