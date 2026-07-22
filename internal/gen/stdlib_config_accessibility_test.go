package gen

import (
	"bytes"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func configConsumerModule(t *testing.T, source string) string {
	t.Helper()
	dir := t.TempDir()
	std, err := filepath.Abs("../../std")
	if err != nil {
		t.Fatal(err)
	}
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/configaccess\n\ngo 1.25.0\n\nrequire goforge.dev/goplus/std v0.0.0\nreplace goforge.dev/goplus/std => "+std+"\n")
	writeRefinementTestFile(t, dir, "main.gp", source)
	return dir
}

func TestGoPlusConsumesSchemaIndexedConfig(t *testing.T) {
	dir := configConsumerModule(t, `package main

import (
	"fmt"
	"goforge.dev/goplus/std/config"
)

func read(0 s nat, snapshot config.Snapshot[s], key config.Key[int, s]) config.Lookup[int] {
	return config.Get(snapshot, key)
}

func main() {
	snapshot := config.Resolve(7, config.Layer{Source: config.FileSource(), Values: map[string]any{"port": 8080}})
	port := config.NewKey[int](7, "port", func(value any) (int, bool) { n, ok := value.(int); return n, ok })
	match read(7, snapshot, port) {
	case config.Found(value, _): fmt.Println(value)
	case config.Missing(): fmt.Println("missing")
	case config.WrongType(_, _): fmt.Println("wrong")
	}
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if !res.Ok() {
		t.Fatalf("generation diagnostics: %+v", res.Diags)
	}
	cmd := exec.Command("go", "run", "-mod=mod", ".")
	cmd.Dir = dir
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("Go+ config consumer: %v\n%s", err, stderr.Bytes())
	}
	if got := stdout.String(); got != "8080\n" {
		t.Fatalf("output = %q", got)
	}
}

func TestSchemaIndexedConfigRejectsForeignKey(t *testing.T) {
	dir := configConsumerModule(t, `package main

import "goforge.dev/goplus/std/config"

func read(0 s nat, snapshot config.Snapshot[s], key config.Key[int, s]) {}

func main() {
	snapshot := config.Resolve(7)
	foreign := config.NewKey[int](8, "port", func(value any) (int, bool) { n, ok := value.(int); return n, ok })
	read(7, snapshot, foreign)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("foreign schema key unexpectedly type checked")
	}
	found := false
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "dependent index mismatch") {
			found = true
		}
	}
	if !found {
		t.Fatalf("diagnostics do not explain schema mismatch: %+v", res.Diags)
	}
}

func TestSchemaIndexedConfigRejectsForeignProjection(t *testing.T) {
	dir := configConsumerModule(t, `package main

import "goforge.dev/goplus/std/config"

func main() {
	snapshot := config.Resolve(7)
	foreign := config.NewSubset(8, 9, "port")
	_ = config.Project(7, 9, snapshot, foreign)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("foreign schema projection unexpectedly type checked")
	}
	found := false
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "dependent index mismatch") {
			found = true
		}
	}
	if !found {
		t.Fatalf("diagnostics do not explain projection mismatch: %+v", res.Diags)
	}
}
