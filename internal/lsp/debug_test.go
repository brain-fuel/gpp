package lsp

import (
	"os"
	"testing"

	"goforge.dev/goplus/internal/sourcemap"
)

func TestMapsBuiltAfterDiagnostics(t *testing.T) {
	dir, path := fixtureModule(t, goodSrc)
	s := &Server{
		conn:     newConn(devNull{}, os.Stderr),
		root:     dir,
		overlays: map[string][]byte{path: []byte(goodSrc)},
		outputs:  map[string][]byte{},
		maps:     map[string]*sourcemap.Map{},
	}
	s.runDiagnostics()
	if len(s.maps) == 0 {
		t.Fatalf("no maps; outputs=%d", len(s.outputs))
	}
	gen := generatedCounterpart(path)
	m := s.maps[gen]
	if m == nil {
		keys := []string{}
		for k := range s.maps {
			keys = append(keys, k)
		}
		t.Fatalf("no map for %s; have %v", gen, keys)
	}
	// Forward the fmt.Println line.
	fwd, ok := forwardPos(m, 20, 2)
	if !ok {
		t.Fatal("forward failed for hover line")
	}
	t.Logf("forward: %+v", fwd)
}

type devNull struct{}

func (devNull) Read(p []byte) (int, error)  { select {} } // blocks: the probe never reads
func (devNull) Write(p []byte) (int, error) { return len(p), nil }

func TestStartGopls(t *testing.T) {
	dir, _ := fixtureModule(t, goodSrc)
	c := startGopls(dir)
	if c == nil {
		t.Fatal("startGopls returned nil")
	}
	defer c.stop()
	t.Log("gopls started and initialized")
}
