package parsec

import (
	"io"
	"strings"
	"testing"
)

// chunkReader yields at most n bytes per Read — the adversarial reader
// for split-rune and compaction behavior.
type chunkReader struct {
	s string
	i int
	n int
}

func (c *chunkReader) Read(p []byte) (int, error) {
	if c.i >= len(c.s) {
		return 0, io.EOF
	}
	end := c.i + c.n
	if end > len(c.s) {
		end = len(c.s)
	}
	m := copy(p, c.s[c.i:end])
	c.i += m
	return m, nil
}

func drain(t *testing.T, in Input) (string, Input) {
	t.Helper()
	var b strings.Builder
	for {
		r, size, eof, err := in.PeekRune()
		if err != nil {
			t.Fatal(err)
		}
		if eof {
			return b.String(), in
		}
		b.WriteRune(r)
		in = in.Advance(r, size)
	}
}

func TestDrainSimple(t *testing.T) {
	in := StartInput(NewStream(strings.NewReader("héllo\nwörld")))
	got, end := drain(t, in)
	if got != "héllo\nwörld" {
		t.Fatalf("drained %q", got)
	}
	if end.Line != 2 || end.Col != 6 {
		t.Fatalf("end position %d:%d", end.Line, end.Col)
	}
}

func TestSplitRunesEveryChunkSize(t *testing.T) {
	src := "aé漢🎉z" // 1-, 2-, 3-, 4-byte runes
	for n := 1; n <= 5; n++ {
		in := StartInput(NewStream(&chunkReader{s: src, n: n}))
		got, _ := drain(t, in)
		if got != src {
			t.Fatalf("chunk=%d drained %q", n, got)
		}
	}
}

func TestCompactionDiscardsBehind(t *testing.T) {
	src := strings.Repeat("x", 20000) + "!"
	in := StartInput(NewStream(&chunkReader{s: src, n: 512}))
	got, _ := drain(t, in)
	if len(got) != 20001 {
		t.Fatalf("drained %d bytes", len(got))
	}
	if in.S.base == 0 {
		t.Fatal("buffer never compacted")
	}
}

func TestPinRetainsForRewind(t *testing.T) {
	src := strings.Repeat("a", 10000) + "b"
	in := StartInput(NewStream(&chunkReader{s: src, n: 256}))
	unpin := in.Pin()
	// Consume far past the pin; the buffer must retain from offset 0.
	cur := in
	for i := 0; i < 10000; i++ {
		r, size, _, err := cur.PeekRune()
		if err != nil {
			t.Fatal(err)
		}
		cur = cur.Advance(r, size)
	}
	if in.S.base != 0 {
		t.Fatalf("pinned bytes discarded (base=%d)", in.S.base)
	}
	// Rewind to the pinned input and re-read.
	r, _, _, err := in.PeekRune()
	if err != nil || r != 'a' {
		t.Fatalf("rewound read %q err=%v", r, err)
	}
	unpin()
	// After unpinning, further reads may compact.
	_, end := drain(t, cur)
	_ = end
	if in.S.base == 0 {
		t.Fatal("buffer never compacted after unpin")
	}
}

func TestInvalidUTF8SurfacesReplacement(t *testing.T) {
	in := StartInput(NewStream(strings.NewReader("a\xffb")))
	got, _ := drain(t, in)
	if got != "a�b" {
		t.Fatalf("drained %q", got)
	}
}
