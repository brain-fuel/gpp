package bddtest

import (
	"fmt"
	"go/token"
	"os"
	"path/filepath"
	"strings"

	"github.com/cucumber/godog"

	"goforge.dev/goplus/internal/directive"
	"goforge.dev/goplus/internal/syntax"
)

// parseState holds frontend-parsing results for the current scenario.
type parseState struct {
	file *syntax.File
	err  error
}

func initParsingSteps(sc *godog.ScenarioContext, w func() *World, ps *parseState) {
	sc.Step(`^a Go\+ file "([^"]+)":$`, func(name string, doc *godog.DocString) error {
		world := w()
		world.LastGoplusFile = name
		return world.writeFile(name, doc.Content)
	})

	sc.Step(`^I parse it$`, func() error {
		world := w()
		if world.LastGoplusFile == "" {
			return fmt.Errorf("no Go+ file was written in this scenario")
		}
		src, err := os.ReadFile(filepath.Join(world.Dir, world.LastGoplusFile))
		if err != nil {
			return err
		}
		ps.file, ps.err = syntax.ParseFile(token.NewFileSet(), world.LastGoplusFile, src)
		return nil
	})

	sc.Step(`^parsing succeeds with (\d+) generic methods?$`, func(want int) error {
		if ps.err != nil {
			return fmt.Errorf("parsing failed: %v", ps.err)
		}
		if got := len(ps.file.Methods); got != want {
			return fmt.Errorf("found %d generic methods, want %d", got, want)
		}
		return nil
	})

	sc.Step(`^parsing fails with an error containing "([^"]*)"$`, func(want string) error {
		if ps.err == nil {
			return fmt.Errorf("parsing succeeded, expected an error containing %q", want)
		}
		if !strings.Contains(ps.err.Error(), want) {
			return fmt.Errorf("error %q does not contain %q", ps.err.Error(), want)
		}
		return nil
	})

	sc.Step(`^generic method (\d+) is "([^"]*)"$`, func(idx int, want string) error {
		m, err := methodAt(ps, idx)
		if err != nil {
			return err
		}
		if got := renderMethod(m); got != want {
			return fmt.Errorf("generic method %d is %q, want %q", idx, got, want)
		}
		return nil
	})

}

func methodAt(ps *parseState, idx int) (*syntax.GenericMethod, error) {
	if ps.err != nil {
		return nil, fmt.Errorf("parsing failed: %v", ps.err)
	}
	if idx < 1 || idx > len(ps.file.Methods) {
		return nil, fmt.Errorf("no generic method %d (have %d)", idx, len(ps.file.Methods))
	}
	return ps.file.Methods[idx-1], nil
}

// renderMethod renders "(Stack[T]) Map[U]" for assertion against features.
func renderMethod(m *syntax.GenericMethod) string {
	var tparams []string
	for _, field := range m.Decl.Type.TypeParams.List {
		for _, name := range field.Names {
			tparams = append(tparams, name.Name)
		}
	}
	mk := directive.Marker{
		Pointer:       m.RecvPointer,
		RecvType:      m.RecvTypeName,
		RecvTParams:   strings.Join(m.RecvTParams, ", "),
		Method:        m.Decl.Name.Name,
		MethodTParams: strings.Join(tparams, ", "),
	}
	// Marker.String renders "//goplus:method (Stack[T]) Map[U]"; strip the prefix.
	return strings.TrimPrefix(mk.String(), "//goplus:method ")
}
