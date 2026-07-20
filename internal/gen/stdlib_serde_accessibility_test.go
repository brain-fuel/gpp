package gen

import (
	"os/exec"
	"path/filepath"
	"testing"
)

// This is deliberately a .gp consumer in a separate module. The stdlib
// serialization APIs are authored as ordinary Go so Go and Go+ users see the
// same generic serde surface without adapters or generated package internals.
func TestGoPlusConsumesCBORSerdeAndDAGProof(t *testing.T) {
	dir := t.TempDir()
	std, err := filepath.Abs("../../std")
	if err != nil {
		t.Fatal(err)
	}
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/serdeaccess\n\ngo 1.24.0\n\nrequire goforge.dev/goplus/std v0.0.0\nreplace goforge.dev/goplus/std => "+std+"\n")
	writeRefinementTestFile(t, dir, "main.gp", `package main

import (
	"fmt"

	"goforge.dev/goplus/std/cbor"
	"goforge.dev/goplus/std/dagcbor"
	"goforge.dev/goplus/std/serde"
)

type Message struct {
	Name string `+"`cbor:\"name\"`"+`
}

func roundTrip[T any](codec serde.Codec[T], value T) (T, error) {
	data, err := serde.Marshal(codec, value)
	if err != nil {
		var zero T
		return zero, err
	}
	return serde.Unmarshal(codec, data)
}

func main() {
	message, err := roundTrip(cbor.Codec[Message]{}, Message{Name: "Go+"})
	if err != nil {
		panic(err)
	}
	proof, err := dagcbor.MarshalProved(message)
	if err != nil {
		panic(err)
	}
	verified, err := dagcbor.Prove[Message](proof.Bytes())
	if err != nil {
		panic(err)
	}
	fmt.Println(verified.Value().Name, len(verified.Bytes()) > 0)
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
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("Go+ serde consumer: %v\n%s", err, out)
	}
	if got := string(out); got != "Go+ true\n" {
		t.Fatalf("output = %q", got)
	}
}
