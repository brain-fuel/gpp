// Package cli implements the gpp command-line interface. It is a separate
// package from cmd/gpp so the Godog spec suite can drive the CLI in-process.
package cli

import (
	"goforge.dev/gpp/internal/version"

	"fmt"
	"io"
)

// Version is the gpp toolchain version reported by `gpp version`.
const Version = version.Version

const usageText = `gpp is the G++ toolchain: a strict superset of Go that emits portable Go.

Usage:

	gpp <command> [arguments]

Commands:

	gen      generate Go from .gpp files (flags: -check, -stage)
	init     scaffold //go:generate wiring for this package (flag: -hook)
	build    generate, then run 'go build'
	test     generate, then run 'go test'
	run      generate, then run 'go run'
	vet      generate, then run 'go vet'
	version  print gpp version
	help     print this help
`

// Run executes the gpp CLI and returns its exit code.
//
// Exit codes: 0 success; 1 stale outputs under gen -check; 2 usage errors or
// G++ diagnostics; delegated go commands pass their exit code through.
func Run(args []string, stdout, stderr io.Writer) int {
	if len(args) == 0 {
		fmt.Fprint(stderr, usageText)
		return 2
	}
	cmd, rest := args[0], args[1:]
	switch cmd {
	case "gen":
		return runGen(rest, stdout, stderr)
	case "init":
		return runInit(rest, stdout, stderr)
	case "build", "test", "run", "vet":
		return runDelegated(cmd, rest, stdout, stderr)
	case "version":
		fmt.Fprintf(stdout, "gpp version %s\n", Version)
		return 0
	case "help", "-h", "--help":
		fmt.Fprint(stdout, usageText)
		return 0
	default:
		fmt.Fprintf(stderr, "gpp: unknown command %q\nRun 'gpp help' for usage.\n", cmd)
		return 2
	}
}
