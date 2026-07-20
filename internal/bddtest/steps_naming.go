package bddtest

import (
	"fmt"
	"go/token"
	"os"
	"path/filepath"
	"strings"

	"github.com/cucumber/godog"

	"goforge.dev/goplus/internal/naming"
	"goforge.dev/goplus/internal/registry"
	"goforge.dev/goplus/internal/syntax"
)

type namingState struct {
	recvType, method string

	loweredNames []string
	errs         []error
}

func initNamingSteps(sc *godog.ScenarioContext, w func() *World, ns *namingState) {
	sc.Step(`^a receiver type "([^"]+)" and method "([^"]+)"$`, func(recvType, method string) error {
		ns.recvType, ns.method = recvType, method
		return nil
	})
	sc.Step(`^the lowered function name is "([^"]+)"$`, func(want string) error {
		got := naming.BareName(ns.recvType, ns.method)
		if got != want {
			return fmt.Errorf("BareName(%q, %q) = %q, want %q", ns.recvType, ns.method, got, want)
		}
		return nil
	})
	sc.Step(`^the prefixed lowered function name is "([^"]+)"$`, func(want string) error {
		got := naming.PrefixedName(ns.recvType, ns.method)
		if got != want {
			return fmt.Errorf("PrefixedName(%q, %q) = %q, want %q", ns.recvType, ns.method, got, want)
		}
		return nil
	})

	sc.Step(`^I compute lowered names$`, func() error {
		world := w()
		src, err := os.ReadFile(filepath.Join(world.Dir, world.LastGoplusFile))
		if err != nil {
			return err
		}
		fset := token.NewFileSet()
		f, err := syntax.ParseFile(fset, world.LastGoplusFile, src)
		if err != nil {
			return fmt.Errorf("parse: %w", err)
		}
		tbl := naming.NewTable()
		for _, d := range naming.TopLevelDecls(fset, f.AST) {
			tbl.AddAuthored(d.Name, d.Position)
		}
		shared := map[string]int{}
		for _, gm := range f.Methods {
			shared[naming.BareName(gm.RecvTypeName, gm.Decl.Name.Name)]++
		}
		methods, errs := registry.MethodsFromFile("example.test/pkg", f, tbl, shared)
		ns.errs = errs
		ns.loweredNames = nil
		for _, m := range methods {
			ns.loweredNames = append(ns.loweredNames, m.FuncName)
		}
		return nil
	})
	sc.Step(`^name generation fails with an error containing "([^"]*)"$`, func(want string) error {
		if len(ns.errs) == 0 {
			return fmt.Errorf("name generation succeeded (%v), expected error containing %q", ns.loweredNames, want)
		}
		var all []string
		for _, e := range ns.errs {
			if strings.Contains(e.Error(), want) {
				return nil
			}
			all = append(all, e.Error())
		}
		return fmt.Errorf("no error contains %q; errors:\n%s", want, strings.Join(all, "\n"))
	})
	sc.Step(`^the lowered names are "([^"]*)"$`, func(want string) error {
		if len(ns.errs) > 0 {
			return fmt.Errorf("unexpected errors: %v", ns.errs)
		}
		got := strings.Join(ns.loweredNames, ", ")
		if got != want {
			return fmt.Errorf("lowered names = %q, want %q", got, want)
		}
		return nil
	})
}
