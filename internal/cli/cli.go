// Package cli implements the goplus command-line interface. It is a separate
// package from cmd/goplus so the Godog spec suite can drive the CLI in-process.
package cli

import (
	"goforge.dev/goplus/internal/lsp"
	"goforge.dev/goplus/internal/version"
	"os"

	"fmt"
	"io"
)

// Version is the goplus toolchain version reported by `goplus version`.
const Version = version.Version

const usageText = `goplus is the Go+ toolchain: a strict superset of Go that emits portable Go.

Usage:

	goplus <command> [arguments]

Commands:

	gen      generate Go from .gp files (flags: -check, -stage)
	init     scaffold //go:generate wiring for this package (flag: -hook)
	lsp      speak the Language Server Protocol over stdio
	build    generate, then run 'go build'
	test     generate, then run 'go test'
	run      generate, then run 'go run'
	vet      generate, then run 'go vet'
	version  print goplus version
	help     print this help
`

// Run executes the goplus CLI and returns its exit code.
//
// Exit codes: 0 success; 1 stale outputs under gen -check; 2 usage errors or
// Go+ diagnostics; delegated go commands pass their exit code through.
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
	case "lsp":
		if err := lsp.Serve(os.Stdin, stdout); err != nil {
			fmt.Fprintf(stderr, "goplus lsp: %v\n", err)
			return 1
		}
		return 0
	case "build", "test", "run", "vet":
		return runDelegated(cmd, rest, stdout, stderr)
	case "version":
		fmt.Fprintf(stdout, "goplus version %s\n", Version)
		return 0
	case "help", "-h", "--help":
		fmt.Fprint(stdout, usageText)
		return 0
	default:
		fmt.Fprintf(stderr, "goplus: unknown command %q\nRun 'goplus help' for usage.\n", cmd)
		return 2
	}
}
