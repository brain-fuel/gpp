package websocket

import (
	"bufio"
	"crypto/rand"
	"errors"
	"io"
	"net"
	"sync"
	"sync/atomic"
	"time"
	"unicode/utf8"
)

// Conn is a concurrency-safe WebSocket connection. One reader and one writer
// may operate concurrently; writes are serialized so frames never interleave.
type Conn struct {
	rw            io.ReadWriteCloser
	br            *bufio.Reader
	side          Side
	assembler     Assembler
	readMu        sync.Mutex
	writeMu       sync.Mutex
	closeOnce     sync.Once
	closeSent     atomic.Bool
	maxFrame      int64
	compression   bool
	writeWindow   int
	manualControl bool
	handshake     HandshakeProtocol
}

// HandshakeProtocol reports whether RFC 6455 Upgrade or RFC 8441 extended
// CONNECT established the connection.
func (c *Conn) HandshakeProtocol() HandshakeProtocol { return c.handshake }

type ConnConfig struct {
	MaxFrame   int64
	MaxMessage int64
	// ManualControl surfaces Ping messages instead of answering them
	// automatically. Close handshake responses remain automatic.
	ManualControl bool
}

func NewConn(rw io.ReadWriteCloser, side Side, buffered *bufio.Reader, cfg ConnConfig) *Conn {
	if cfg.MaxFrame <= 0 {
		cfg.MaxFrame = 16 << 20
	}
	if cfg.MaxMessage <= 0 {
		cfg.MaxMessage = 64 << 20
	}
	if cfg.MaxFrame > cfg.MaxMessage {
		cfg.MaxFrame = cfg.MaxMessage
	}
	if buffered == nil {
		buffered = bufio.NewReaderSize(rw, 4096)
	}
	return &Conn{rw: rw, br: buffered, side: side, maxFrame: cfg.MaxFrame, manualControl: cfg.ManualControl, assembler: Assembler{MaxMessage: cfg.MaxMessage}}
}

func (c *Conn) NetConn() net.Conn { n, _ := c.rw.(net.Conn); return n }
func (c *Conn) SetDeadline(t time.Time) error {
	if n := c.NetConn(); n != nil {
		return n.SetDeadline(t)
	}
	return nil
}
func (c *Conn) SetReadDeadline(t time.Time) error {
	if n := c.NetConn(); n != nil {
		return n.SetReadDeadline(t)
	}
	return nil
}
func (c *Conn) SetWriteDeadline(t time.Time) error {
	if n := c.NetConn(); n != nil {
		return n.SetWriteDeadline(t)
	}
	return nil
}

func (c *Conn) readFrame() (Header, []byte, error) {
	var raw [14]byte
	if _, err := io.ReadFull(c.br, raw[:2]); err != nil {
		return Header{}, nil, err
	}
	n := 2
	switch raw[1] & 0x7f {
	case 126:
		n += 2
	case 127:
		n += 8
	}
	if raw[1]&0x80 != 0 {
		n += 4
	}
	if _, err := io.ReadFull(c.br, raw[2:n]); err != nil {
		return Header{}, nil, err
	}
	h, _, err := ParseHeader(raw[:n], c.side, c.compression)
	if err != nil {
		return Header{}, nil, err
	}
	if h.Length > c.maxFrame || uint64(h.Length) > uint64(^uint(0)>>1) {
		return Header{}, nil, &failureDetail{cause: ErrMessageTooLarge, limit: c.maxFrame}
	}
	payload := make([]byte, int(h.Length))
	if _, err = io.ReadFull(c.br, payload); err != nil {
		return Header{}, nil, err
	}
	if h.Masked {
		Mask(payload, h.Mask, 0)
	}
	return h, payload, nil
}

// ReadMessage returns the next complete data or close message. Ping is
// answered automatically; Pong is surfaced so applications can track liveness.
func (c *Conn) ReadMessage() (Message, error) {
	c.readMu.Lock()
	defer c.readMu.Unlock()
	for {
		h, payload, err := c.readFrame()
		if err != nil {
			c.failProtocol(err)
			return nil, err
		}
		msg, err := c.assembler.feed(h, payload, false)
		if err != nil {
			c.failProtocol(err)
			return nil, err
		}
		if msg == nil {
			continue
		}
		switch m := msg.(type) {
		case PingMessage:
			if c.manualControl {
				return msg, nil
			}
			if err := c.writeFrameOwned(OpPong, m.Payload); err != nil {
				return nil, err
			}
			continue
		case CloseMessage:
			body, buildErr := AppendClosePayload(nil, m.Code, m.Reason)
			if buildErr == nil {
				_ = c.writeClose(body)
			}
			return msg, io.EOF
		default:
			return msg, nil
		}
	}
}

func (c *Conn) failProtocol(cause error) {
	var code CloseCode
	switch {
	case errors.Is(cause, ErrInvalidUTF8):
		code = CloseInvalidPayload
	case errors.Is(cause, ErrMessageTooLarge):
		code = CloseMessageTooBig
	case errors.Is(cause, ErrInvalidOpcode), errors.Is(cause, ErrReservedBits), errors.Is(cause, ErrWrongMask),
		errors.Is(cause, ErrNonCanonicalLength), errors.Is(cause, ErrControlFragmented), errors.Is(cause, ErrControlTooLarge),
		errors.Is(cause, ErrUnexpectedContinuation), errors.Is(cause, ErrExpectedContinuation),
		errors.Is(cause, ErrInvalidClosePayload), errors.Is(cause, ErrInvalidCloseCode):
		code = CloseProtocolError
	default:
		return
	}
	body, _ := AppendClosePayload(nil, code, "")
	_ = c.writeClose(body)
}

func (c *Conn) WriteMessage(message Message) error {
	return c.writeMessage(message, false)
}

// WriteText and WriteBinary are concise Go-facing forms of WriteMessage.
func (c *Conn) WriteText(payload []byte) error {
	return c.writeDataFrameChecked(OpText, payload, false)
}

func (c *Conn) WriteBinary(payload []byte) error {
	return c.writeDataFrame(OpBinary, payload, false)
}

// WriteTextOwned and WriteBinaryOwned transfer payload ownership, allowing a
// client connection to mask in place instead of making a defensive copy.
func (c *Conn) WriteTextOwned(payload []byte) error {
	return c.writeDataFrameChecked(OpText, payload, true)
}

func (c *Conn) WriteBinaryOwned(payload []byte) error {
	return c.writeDataFrame(OpBinary, payload, true)
}

func (c *Conn) WritePing(payload []byte) error {
	return c.writeFrame(OpPing, payload)
}

func (c *Conn) WritePong(payload []byte) error {
	return c.writeFrame(OpPong, payload)
}

// WriteClose starts the RFC 6455 closing handshake without immediately
// closing the underlying transport.
func (c *Conn) WriteClose(code CloseCode, reason string) error {
	payload, err := AppendClosePayload(nil, code, reason)
	if err != nil {
		return err
	}
	return c.writeClose(payload)
}

// WriteMessageOwned may mask the message payload in place on client
// connections. Callers that transfer ownership can use it to avoid the one
// defensive payload copy required by WriteMessage.
func (c *Conn) WriteMessageOwned(message Message) error {
	return c.writeMessage(message, true)
}

func (c *Conn) writeMessage(message Message, owned bool) error {
	switch m := message.(type) {
	case TextMessage:
		return c.writeDataFrameChecked(OpText, m.Payload, owned)
	case BinaryMessage:
		return c.writeDataFrame(OpBinary, m.Payload, owned)
	case PingMessage:
		return c.writeFrameMaybeOwned(OpPing, m.Payload, owned)
	case PongMessage:
		return c.writeFrameMaybeOwned(OpPong, m.Payload, owned)
	case CloseMessage:
		body, err := AppendClosePayload(nil, m.Code, m.Reason)
		if err != nil {
			return err
		}
		return c.writeClose(body)
	default:
		return errors.New("websocket: unknown message")
	}
}

func (c *Conn) writeDataFrameChecked(op Opcode, payload []byte, owned bool) error {
	if op == OpText && !utf8.Valid(payload) {
		return ErrInvalidUTF8
	}
	return c.writeDataFrame(op, payload, owned)
}

func (c *Conn) enableCompression(settings compressionSettings) {
	c.compression = true
	if settings.writeWindow == 0 {
		settings.writeWindow = 15
	}
	if settings.readWindow == 0 {
		settings.readWindow = 15
	}
	c.writeWindow = settings.writeWindow
	inflater := &messageInflater{window: settings.readWindow, context: settings.readContext}
	c.assembler.inflate = inflater.inflate
}

func (c *Conn) writeDataFrame(op Opcode, payload []byte, owned bool) error {
	if !c.compression {
		return c.writeFrameMaybeOwned(op, payload, owned)
	}
	body, err := deflateMessage(payload, c.writeWindow)
	if err != nil {
		return err
	}
	return c.writeFrameRSV1(op, body, true, true)
}

func (c *Conn) writeFrame(op Opcode, payload []byte) error {
	return c.writeFrameRSV1(op, payload, false, false)
}

func (c *Conn) writeFrameOwned(op Opcode, payload []byte) error {
	return c.writeFrameRSV1(op, payload, false, true)
}

func (c *Conn) writeFrameMaybeOwned(op Opcode, payload []byte, owned bool) error {
	return c.writeFrameRSV1(op, payload, false, owned)
}

func (c *Conn) writeFrameRSV1(op Opcode, payload []byte, rsv1, owned bool) error {
	if IsControl(op) && len(payload) > 125 {
		return ErrControlTooLarge
	}
	c.writeMu.Lock()
	defer c.writeMu.Unlock()
	if op != OpClose && c.closeSent.Load() {
		return net.ErrClosed
	}
	h := Header{FIN: true, RSV1: rsv1, Opcode: op, Length: int64(len(payload)), Masked: c.side == ClientSide}
	body := payload
	if h.Masked {
		if _, err := io.ReadFull(rand.Reader, h.Mask[:]); err != nil {
			return err
		}
		if !owned {
			body = append([]byte(nil), payload...)
		}
		Mask(body, h.Mask, 0)
	}
	var storage [14]byte
	header := appendHeader(storage[:0], h)
	if _, ok := c.rw.(net.Conn); ok {
		bufs := net.Buffers{header, body}
		_, err := bufs.WriteTo(c.rw)
		return err
	}
	if err := writeAll(c.rw, header); err != nil {
		return err
	}
	return writeAll(c.rw, body)
}

func writeAll(w io.Writer, payload []byte) error {
	for len(payload) != 0 {
		n, err := w.Write(payload)
		if err != nil {
			return err
		}
		if n <= 0 || n > len(payload) {
			return io.ErrShortWrite
		}
		payload = payload[n:]
	}
	return nil
}

func (c *Conn) writeClose(payload []byte) error {
	if !c.closeSent.CompareAndSwap(false, true) {
		return net.ErrClosed
	}
	return c.writeFrameOwned(OpClose, payload)
}

func (c *Conn) Close() error {
	var err error
	c.closeOnce.Do(func() { err = c.rw.Close() })
	return err
}
