package cli

import (
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"strings"

	"goforge.dev/goplus/internal/diag"
	"goforge.dev/goplus/internal/gen"
	"goforge.dev/goplus/internal/toolchain"
)

func runGen(args []string, stdout, stderr io.Writer) int {
	fs := flag.NewFlagSet("goplus gen", flag.ContinueOnError)
	fs.SetOutput(stderr)
	check := fs.Bool("check", false, "verify generated files are current; write nothing (exit 1 when stale)")
	stage := fs.Bool("stage", false, "git-add written and deleted files after generating")
	if err := fs.Parse(args); err != nil {
		return 2
	}
	cwd, err := os.Getwd()
	if err != nil {
		fmt.Fprintf(stderr, "goplus: %v\n", err)
		return 2
	}
	res, err := gen.Run(gen.Options{Dir: cwd, Patterns: fs.Args(), Check: *check, Stage: *stage})
	if err != nil {
		fmt.Fprintf(stderr, "goplus: %v\n", err)
		return 2
	}
	if !res.Ok() {
		diag.Render(stderr, res.Diags)
		return 2
	}
	if *check && len(res.Stale) > 0 {
		fmt.Fprintln(stderr, "goplus: stale generated code:")
		for _, path := range res.Stale {
			fmt.Fprintf(stderr, "  %s\n", path)
		}
		fmt.Fprintln(stderr, "run `goplus gen ./...` and re-stage.")
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
		fmt.Fprintf(stderr, "goplus: %v\n", err)
		return 2
	}
	res, err := gen.Run(gen.Options{Dir: cwd, Patterns: []string{"./..."}})
	if err != nil {
		fmt.Fprintf(stderr, "goplus: %v\n", err)
		return 2
	}
	if !res.Ok() {
		diag.Render(stderr, res.Diags)
		return 2
	}
	return toolchain.Go(cwd, sub, args, stdout, stderr)
}

// runInit scaffolds the go-generate wiring: a goplus_generate.go carrying
// the //go:generate directive, so `go generate ./...` regenerates the
// module and plain `go build` takes it from there — the canonical
// workflow, with the goplus wrapper as convenience. -hook also writes a
// pre-commit config entry.
func runInit(args []string, stdout, stderr io.Writer) int {
	hook := false
	for _, a := range args {
		switch a {
		case "-hook", "--hook":
			hook = true
		default:
			fmt.Fprintf(stderr, "goplus init: unknown argument %q\n", a)
			return 2
		}
	}
	pkg, err := detectPackageName(".")
	if err != nil {
		fmt.Fprintf(stderr, "goplus init: %v\n", err)
		return 2
	}
	const genFile = "goplus_generate.go"
	if _, err := os.Stat(genFile); err == nil {
		fmt.Fprintf(stderr, "goplus init: %s already exists\n", genFile)
		return 2
	}
	content := "// Scaffolded by goplus init. `go generate ./...` regenerates every\n" +
		"// *_gp.go in the module; plain `go build` works from there.\n\n" +
		"//go:generate go tool goplus gen ./...\n\n" +
		"package " + pkg + "\n"
	if err := os.WriteFile(genFile, []byte(content), 0o644); err != nil {
		fmt.Fprintf(stderr, "goplus init: %v\n", err)
		return 2
	}
	fmt.Fprintf(stdout, "wrote %s\n", genFile)
	if hook {
		const hookFile = ".pre-commit-config.yaml"
		if _, err := os.Stat(hookFile); err == nil {
			fmt.Fprintf(stdout, "%s already exists; add the goplus hook from the README manually\n", hookFile)
		} else {
			hookYAML := "repos:\n" +
				"  - repo: https://github.com/brain-fuel/goplus\n" +
				"    rev: " + Version + "\n" +
				"    hooks:\n" +
				"      - id: goplus-gen\n"
			if err := os.WriteFile(hookFile, []byte(hookYAML), 0o644); err != nil {
				fmt.Fprintf(stderr, "goplus init: %v\n", err)
				return 2
			}
			fmt.Fprintf(stdout, "wrote %s\n", hookFile)
		}
	}
	fmt.Fprintf(stdout, "next steps:\n")
	fmt.Fprintf(stdout, "\tgo get -tool goforge.dev/goplus/cmd/goplus@latest   # pins goplus in go.mod (Go 1.24+)\n")
	fmt.Fprintf(stdout, "\tgo generate ./...                             # regenerate\n")
	fmt.Fprintf(stdout, "\tgo build ./...                                # plain Go from here\n")
	return 0
}

// detectPackageName reads the package clause of any Go or Go+ file in
// dir, defaulting to "main" in an empty directory.
func detectPackageName(dir string) (string, error) {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return "", err
	}
	re := regexp.MustCompile(`(?m)^package\s+(\w+)`)
	for _, e := range entries {
		name := e.Name()
		if e.IsDir() || (!strings.HasSuffix(name, ".go") && !strings.HasSuffix(name, ".gp")) {
			continue
		}
		src, rerr := os.ReadFile(filepath.Join(dir, name))
		if rerr != nil {
			continue
		}
		if m := re.FindSubmatch(src); m != nil {
			return string(m[1]), nil
		}
	}
	return "main", nil
}
