// Streaming input for parsec (plain Go: this is IO machinery; the
// combinator layer above it is authored in gpp). A Stream buffers an
// io.Reader; an Input is a VALUE — (stream, absolute offset, line,
// col) — so replies can carry rest-of-input and alternatives can hold
// older Inputs. The consumed/empty discipline bounds backtracking: the
// buffer must retain bytes from the lowest live pin (a Try in flight)
// or the current read point, and may discard everything earlier —
// which is why positions ride along incrementally instead of being
// recomputed.
package parsec

import (
	"io"
	"unicode/utf8"
)

// Stream buffers one reader for one parse. Single-goroutine use.
type Stream struct {
	r    io.Reader
	buf  []byte
	base int // absolute offset of buf[0]
	eof  bool
	pins []int // absolute offsets Try is prepared to rewind to (stack)
}

// NewStream wraps a reader; nil reads as empty input.
func NewStream(r io.Reader) *Stream {
	if r == nil {
		return &Stream{eof: true}
	}
	return &Stream{r: r}
}

// Input is a position in a stream, with the human position alongside.
type Input struct {
	S    *Stream
	Off  int // absolute byte offset
	Line int // 1-based
	Col  int // 1-based, in runes
}

// StartInput begins at offset zero, line 1, column 1.
func StartInput(s *Stream) Input {
	return Input{S: s, Off: 0, Line: 1, Col: 1}
}

// pin marks an absolute offset the stream must retain (Try's rewind
// point). Returns unpin.
func (s *Stream) pin(off int) func() {
	s.pins = append(s.pins, off)
	i := len(s.pins) - 1
	return func() { s.pins = s.pins[:i] }
}

// retainFrom is the lowest offset that must stay buffered.
func (s *Stream) retainFrom(current int) int {
	lo := current
	for _, p := range s.pins {
		if p < lo {
			lo = p
		}
	}
	return lo
}

// fill ensures buf covers [off, off+need) or EOF, compacting first.
func (s *Stream) fill(off, need int, retain int) error {
	if keep := retain - s.base; keep > 0 {
		if keep >= len(s.buf) {
			s.buf = s.buf[:0]
			s.base = retain
		} else {
			s.buf = append(s.buf[:0], s.buf[keep:]...)
			s.base = retain
		}
	}
	for !s.eof && s.base+len(s.buf) < off+need {
		var chunk [4096]byte
		n, err := s.r.Read(chunk[:])
		if n > 0 {
			s.buf = append(s.buf, chunk[:n]...)
		}
		if err == io.EOF {
			s.eof = true
		} else if err != nil {
			return err
		}
	}
	return nil
}

// PeekRune decodes the rune at in.Off without consuming. eof reports
// end of input; err is a read failure.
func (in Input) PeekRune() (r rune, size int, eof bool, err error) {
	s := in.S
	if err := s.fill(in.Off, utf8.UTFMax, s.retainFrom(in.Off)); err != nil {
		return 0, 0, false, err
	}
	rel := in.Off - s.base
	if rel >= len(s.buf) {
		return 0, 0, true, nil
	}
	r, size = utf8.DecodeRune(s.buf[rel:])
	if r == utf8.RuneError && size == 1 && !s.eof {
		// A split rune at the buffer edge would have been filled above;
		// reaching here means genuinely invalid UTF-8 — surface the
		// replacement rune, one byte wide, like the rest of Go.
		return utf8.RuneError, 1, false, nil
	}
	return r, size, false, nil
}

// Advance steps past a rune of the given size, updating line/col.
func (in Input) Advance(r rune, size int) Input {
	out := in
	out.Off += size
	if r == '\n' {
		out.Line++
		out.Col = 1
	} else {
		out.Col++
	}
	return out
}

// Pin marks this input as a rewind point for a Try in flight.
func (in Input) Pin() func() { return in.S.pin(in.Off) }
