package lsp

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"goforge.dev/goplus/internal/version"
)

// testClient runs Serve over in-process pipes.
type testClient struct {
	t     *testing.T
	c     *conn
	notes chan *message
	resps chan *message
}

func startTestServer(t *testing.T) *testClient {
	t.Helper()
	cliR, srvW := io.Pipe()
	srvR, cliW := io.Pipe()
	go func() { _ = Serve(srvR, srvW) }()
	tc := &testClient{t: t, c: newConn(cliR, cliW), notes: make(chan *message, 64), resps: make(chan *message, 16)}
	go func() {
		for {
			m, err := tc.c.read()
			if err != nil {
				close(tc.notes)
				return
			}
			if m.ID != nil {
				tc.resps <- m
			} else {
				tc.notes <- m
			}
		}
	}()
	return tc
}

func (tc *testClient) request(method string, params any) *message {
	tc.t.Helper()
	raw, _ := json.Marshal(params)
	id := json.RawMessage(fmt.Sprintf("%d", time.Now().UnixNano()%1_000_000))
	if err := tc.c.write(&message{ID: &id, Method: method, Params: raw}); err != nil {
		tc.t.Fatal(err)
	}
	select {
	case m := <-tc.resps:
		return m
	case <-time.After(60 * time.Second):
		tc.t.Fatal("timeout waiting for response to " + method)
		return nil
	}
}

func (tc *testClient) notifyServer(method string, params any) {
	tc.t.Helper()
	raw, _ := json.Marshal(params)
	if err := tc.c.write(&message{Method: method, Params: raw}); err != nil {
		tc.t.Fatal(err)
	}
}

func (tc *testClient) awaitDiagnostics(path string, timeout time.Duration) *publishDiagnosticsParams {
	tc.t.Helper()
	deadline := time.After(timeout)
	for {
		select {
		case m, ok := <-tc.notes:
			if !ok {
				tc.t.Fatal("server closed")
			}
			if m.Method != "textDocument/publishDiagnostics" {
				continue
			}
			var p publishDiagnosticsParams
			_ = json.Unmarshal(m.Params, &p)
			if uriToPath(p.URI) == path {
				return &p
			}
		case <-deadline:
			tc.t.Fatalf("no diagnostics for %s", path)
		}
	}
}

// fixtureModule writes a minimal goplus module and returns its dir.
func fixtureModule(t *testing.T, mainSrc string) (string, string) {
	t.Helper()
	dir := t.TempDir()
	dir, _ = filepath.EvalSymlinks(dir)
	if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte("module example.com/lspfix\n\ngo 1.24\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(dir, "main.gp")
	if err := os.WriteFile(path, []byte(mainSrc), 0o644); err != nil {
		t.Fatal(err)
	}
	return dir, path
}

const goodSrc = `package main

import "fmt"

type Shape enum {
	Circle(r float64)
	Square(side float64)
}

func area(s Shape) float64 {
	match s {
	case Circle(r):
		return 3.14 * r * r
	case Square(side):
		return side * side
	}
	return 0
}

func main() {
	fmt.Println(area(Circle(2)))
}
`

func TestInitializeAndDiagnostics(t *testing.T) {
	dir, path := fixtureModule(t, goodSrc)
	tc := startTestServer(t)

	resp := tc.request("initialize", initializeParams{RootURI: pathToURI(dir)})
	out, _ := json.Marshal(resp.Result)
	if !strings.Contains(string(out), `"name":"goplus"`) {
		t.Fatalf("serverInfo missing: %s", out)
	}
	if !strings.Contains(string(out), version.Version) {
		t.Fatalf("server version not locked to toolchain: %s", out)
	}
	tc.notifyServer("initialized", struct{}{})

	// Clean file: empty diagnostics.
	tc.notifyServer("textDocument/didOpen", didOpenParams{TextDocument: textDocumentItem{URI: pathToURI(path), Text: goodSrc}})
	p := tc.awaitDiagnostics(path, 90*time.Second)
	if len(p.Diagnostics) != 0 {
		t.Fatalf("expected clean, got %v", p.Diagnostics)
	}

	// Introduce a non-exhaustive match: a goplus diagnostic with position.
	broken := strings.Replace(goodSrc, "\tcase Square(side):\n\t\treturn side * side\n", "", 1)
	tc.notifyServer("textDocument/didChange", didChangeParams{
		TextDocument: textDocumentIdentifier{URI: pathToURI(path)},
		Changes:      []contentChange{{Text: broken}},
	})
	p = tc.awaitDiagnostics(path, 90*time.Second)
	if len(p.Diagnostics) == 0 {
		t.Fatal("expected a diagnostic")
	}
	if !strings.Contains(p.Diagnostics[0].Message, "non-exhaustive match") {
		t.Fatalf("message: %q", p.Diagnostics[0].Message)
	}
	if p.Diagnostics[0].Range.Start.Line == 0 {
		t.Fatalf("diagnostic not positioned: %+v", p.Diagnostics[0])
	}

	// Fix it again: diagnostics clear.
	tc.notifyServer("textDocument/didChange", didChangeParams{
		TextDocument: textDocumentIdentifier{URI: pathToURI(path)},
		Changes:      []contentChange{{Text: goodSrc}},
	})
	p = tc.awaitDiagnostics(path, 90*time.Second)
	if len(p.Diagnostics) != 0 {
		t.Fatalf("diagnostics did not clear: %v", p.Diagnostics)
	}

	tc.request("shutdown", nil)
	tc.notifyServer("exit", nil)
}

func TestHoverThroughGopls(t *testing.T) {
	if _, err := exec.LookPath("gopls"); err != nil {
		t.Skip("gopls not installed")
	}
	dir, path := fixtureModule(t, goodSrc)
	tc := startTestServer(t)
	tc.request("initialize", initializeParams{RootURI: pathToURI(dir)})
	tc.notifyServer("initialized", struct{}{})
	tc.notifyServer("textDocument/didOpen", didOpenParams{TextDocument: textDocumentItem{URI: pathToURI(path), Text: goodSrc}})
	tc.awaitDiagnostics(path, 90*time.Second)

	// Hover over `fmt` on the Println line (line index of "fmt.Println").
	lines := strings.Split(goodSrc, "\n")
	hline := -1
	for i, l := range lines {
		if strings.Contains(l, "fmt.Println") {
			hline = i
		}
	}
	deadline := time.Now().Add(90 * time.Second)
	for {
		resp := tc.request("textDocument/hover", positionParams{
			TextDocument: textDocumentIdentifier{URI: pathToURI(path)},
			Position:     Position{Line: hline, Character: 2},
		})
		out, _ := json.Marshal(resp.Result)
		if strings.Contains(string(out), "Println") || strings.Contains(string(out), "package fmt") {
			break
		}
		if time.Now().After(deadline) {
			t.Fatalf("hover never resolved: %s", out)
		}
		time.Sleep(2 * time.Second)
	}
	tc.request("shutdown", nil)
	tc.notifyServer("exit", nil)
}
