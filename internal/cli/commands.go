package cli

import (
	"flag"
	"fmt"
	"io"
	"os"

	"goforge.dev/gpp/internal/diag"
	"goforge.dev/gpp/internal/gen"
	"goforge.dev/gpp/internal/toolchain"
)

func runGen(args []string, stdout, stderr io.Writer) int {
	fs := flag.NewFlagSet("gpp gen", flag.ContinueOnError)
	fs.SetOutput(stderr)
	check := fs.Bool("check", false, "verify generated files are current; write nothing (exit 1 when stale)")
	stage := fs.Bool("stage", false, "git-add written and deleted files after generating")
	if err := fs.Parse(args); err != nil {
		return 2
	}
	cwd, err := os.Getwd()
	if err != nil {
		fmt.Fprintf(stderr, "gpp: %v\n", err)
		return 2
	}
	res, err := gen.Run(gen.Options{Dir: cwd, Patterns: fs.Args(), Check: *check, Stage: *stage})
	if err != nil {
		fmt.Fprintf(stderr, "gpp: %v\n", err)
		return 2
	}
	if !res.Ok() {
		diag.Render(stderr, res.Diags)
		return 2
	}
	if *check && len(res.Stale) > 0 {
		fmt.Fprintln(stderr, "gpp: stale generated code:")
		for _, path := range res.Stale {
			fmt.Fprintf(stderr, "  %s\n", path)
		}
		fmt.Fprintln(stderr, "run `gpp gen ./...` and re-stage.")
		return 1
	}
	for _, path := range res.Written {
		fmt.Fprintln(stdout, path)
	}
	return 0
}

// runDelegated regenerates the whole module, then delegates to the go tool.
func runDelegated(sub string, args []string, stdout, stderr io.Writer) int {
	cwd, err := os.Getwd()
	if err != nil {
		fmt.Fprintf(stderr, "gpp: %v\n", err)
		return 2
	}
	res, err := gen.Run(gen.Options{Dir: cwd, Patterns: []string{"./..."}})
	if err != nil {
		fmt.Fprintf(stderr, "gpp: %v\n", err)
		return 2
	}
	if !res.Ok() {
		diag.Render(stderr, res.Diags)
		return 2
	}
	return toolchain.Go(cwd, sub, args, stdout, stderr)
}
