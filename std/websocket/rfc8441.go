package websocket

import (
	"context"
	"crypto/tls"
	"errors"
	"io"
	"net"
	"net/http"
	"net/url"
	"os"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"golang.org/x/net/http2"
)

// HTTP2Mode controls selection of the opening-handshake transport.
type HTTP2Mode uint8

const (
	// HTTP2Auto prefers RFC 8441 for secure WebSockets and falls back to RFC
	// 6455 when the peer does not support extended CONNECT. Cleartext ws uses
	// RFC 6455 unless a custom HTTP2Transport is supplied.
	HTTP2Auto HTTP2Mode = iota
	// HTTP1Only disables RFC 8441 and always uses the RFC 6455 Upgrade.
	HTTP1Only
	// HTTP2Only requires RFC 8441, including h2c prior knowledge for ws URLs.
	HTTP2Only
)

var (
	defaultSecureHTTP2Transport = newHTTP2Transport(DialOptions{}, false)
	defaultClearHTTP2Transport  = newHTTP2Transport(DialOptions{}, true)
)

// HandshakeProtocol identifies how a WebSocket connection was bootstrapped.
type HandshakeProtocol uint8

const (
	RFC6455Handshake HandshakeProtocol = iota
	RFC8441Handshake
)

func (p HandshakeProtocol) String() string {
	if p == RFC8441Handshake {
		return "RFC 8441"
	}
	return "RFC 6455"
}

func dial(ctx context.Context, rawURL string, opts DialOptions) (*Conn, *http.Response, error) {
	u, err := url.Parse(rawURL)
	tryHTTP2 := err == nil && shouldTryHTTP2(u, opts)
	if tryHTTP2 {
		conn, response, h2Err := dialRFC8441(ctx, u, opts)
		if h2Err == nil || opts.HTTP2 == HTTP2Only || ctx.Err() != nil {
			return conn, response, h2Err
		}
		var unavailable *http2UnavailableError
		if !errors.As(h2Err, &unavailable) {
			return nil, response, h2Err
		}
	}
	return dialRFC6455(ctx, rawURL, opts)
}

type http2UnavailableError struct{ cause error }

func (e *http2UnavailableError) Error() string { return e.cause.Error() }
func (e *http2UnavailableError) Unwrap() error { return e.cause }

func isHTTP2Unavailable(err error) bool {
	if err == nil {
		return false
	}
	message := strings.ToLower(err.Error())
	return strings.Contains(message, "extended connect not supported") ||
		strings.Contains(message, "no application protocol") ||
		strings.Contains(message, "unsupported application protocols") ||
		strings.Contains(message, "unexpected alpn protocol") ||
		strings.Contains(message, "could not negotiate protocol mutually")
}

func fallbackStatus(status int) bool {
	switch status {
	case http.StatusNotFound, http.StatusMethodNotAllowed, http.StatusMisdirectedRequest,
		http.StatusUpgradeRequired, http.StatusNotImplemented, http.StatusHTTPVersionNotSupported:
		return true
	default:
		return false
	}
}

func shouldTryHTTP2(u *url.URL, opts DialOptions) bool {
	if opts.HTTP2 == HTTP1Only {
		return false
	}
	return opts.HTTP2 == HTTP2Only || opts.HTTP2Transport != nil || (opts.HTTP2 == HTTP2Auto && u.Scheme == "wss")
}

func validateDialOptions(opts DialOptions) (string, error) {
	seen := make(map[string]struct{}, len(opts.Protocols))
	for _, protocol := range opts.Protocols {
		if !validToken(protocol) {
			return "", ErrHandshake
		}
		if _, duplicate := seen[protocol]; duplicate {
			return "", ErrHandshake
		}
		seen[protocol] = struct{}{}
	}
	if opts.Compression == nil {
		return "", nil
	}
	return compressionOffer(*opts.Compression)
}

func dialRFC8441(ctx context.Context, u *url.URL, opts DialOptions) (*Conn, *http.Response, error) {
	compressionHeader, err := validateDialOptions(opts)
	if err != nil {
		return nil, nil, err
	}
	if (u.Scheme != "ws" && u.Scheme != "wss") || u.Hostname() == "" || u.Fragment != "" {
		return nil, nil, ErrHandshake
	}
	head := opts.Header.Clone()
	if head == nil {
		head = make(http.Header)
	}
	for _, forbidden := range []string{"Connection", "Upgrade", "Host", "Sec-WebSocket-Key", "Sec-WebSocket-Accept", ":protocol"} {
		if len(head.Values(forbidden)) != 0 {
			return nil, nil, ErrHandshake
		}
	}
	head.Set(":protocol", "websocket")
	head.Set("Sec-WebSocket-Version", "13")
	// HTTP content codings must never transform bytes in the WebSocket tunnel.
	head.Set("Accept-Encoding", "identity")
	if len(opts.Protocols) != 0 {
		head.Set("Sec-WebSocket-Protocol", strings.Join(opts.Protocols, ", "))
	}
	if compressionHeader != "" {
		head.Set("Sec-WebSocket-Extensions", compressionHeader)
	}
	scheme := "http"
	if u.Scheme == "wss" {
		scheme = "https"
	}
	target := &url.URL{Scheme: scheme, Host: u.Host, Path: u.Path, RawPath: u.RawPath, RawQuery: u.RawQuery}
	if target.Path == "" {
		target.Path = "/"
	}
	reader, writer := io.Pipe()
	streamContext, cancel := context.WithCancel(context.WithoutCancel(ctx))
	stopCancellation := context.AfterFunc(ctx, cancel)
	req := &http.Request{
		Method:        http.MethodConnect,
		URL:           target,
		Host:          u.Host,
		Header:        head,
		Body:          reader,
		ContentLength: -1,
	}
	req = req.WithContext(streamContext)
	transport := opts.HTTP2Transport
	var closeIdle func()
	if transport == nil {
		customized := opts.TLSConfig != nil || opts.NetDialer != nil || opts.DialContext != nil
		if !customized && u.Scheme == "wss" {
			transport = defaultSecureHTTP2Transport
		} else if !customized && u.Scheme == "ws" {
			transport = defaultClearHTTP2Transport
		} else {
			owned := newHTTP2Transport(opts, u.Scheme == "ws")
			transport = owned
			closeIdle = owned.CloseIdleConnections
		}
	}
	response, err := transport.RoundTrip(req)
	if err != nil {
		stopCancellation()
		cancel()
		_ = writer.CloseWithError(err)
		_ = reader.CloseWithError(err)
		if closeIdle != nil {
			closeIdle()
		}
		if isHTTP2Unavailable(err) {
			return nil, nil, &http2UnavailableError{cause: err}
		}
		return nil, nil, err
	}
	if response.ProtoMajor != 2 || response.StatusCode < 200 || response.StatusCode >= 300 {
		stopCancellation()
		cancel()
		_ = response.Body.Close()
		_ = writer.CloseWithError(ErrHandshake)
		if closeIdle != nil {
			closeIdle()
		}
		if response.ProtoMajor == 2 && fallbackStatus(response.StatusCode) {
			return nil, response, &http2UnavailableError{cause: ErrHandshake}
		}
		return nil, response, ErrHandshake
	}
	settings, err := validateClientHandshakeResponse(response, opts)
	if err != nil {
		stopCancellation()
		cancel()
		_ = response.Body.Close()
		_ = writer.CloseWithError(err)
		if closeIdle != nil {
			closeIdle()
		}
		return nil, response, err
	}
	if !stopCancellation() || ctx.Err() != nil {
		cancel()
		_ = response.Body.Close()
		_ = writer.CloseWithError(ctx.Err())
		return nil, response, ctx.Err()
	}
	streamBody := response.Body
	response.Body = http.NoBody
	stream := newStreamConn(streamBody, writer, cancel)
	if closeIdle != nil {
		stream.onClose = closeIdle
	}
	conn := NewConn(stream, ClientSide, nil, opts.Config)
	conn.handshake = RFC8441Handshake
	if settings.enabled {
		conn.enableCompression(settings.compression)
	}
	return conn, response, nil
}

func newHTTP2Transport(opts DialOptions, cleartext bool) *http2.Transport {
	transport := &http2.Transport{AllowHTTP: cleartext, DisableCompression: true}
	if opts.TLSConfig != nil {
		transport.TLSClientConfig = opts.TLSConfig.Clone()
	}
	dialer := opts.NetDialer
	if dialer == nil {
		dialer = &net.Dialer{Timeout: 30 * time.Second, KeepAlive: 30 * time.Second}
	}
	dial := dialer.DialContext
	if opts.DialContext != nil {
		dial = opts.DialContext
	}
	transport.DialTLSContext = func(ctx context.Context, network, address string, cfg *tls.Config) (net.Conn, error) {
		connection, err := dial(ctx, network, address)
		if err != nil || cleartext {
			return connection, err
		}
		tlsConnection := tls.Client(connection, cfg)
		if err := tlsConnection.HandshakeContext(ctx); err != nil {
			_ = connection.Close()
			return nil, err
		}
		return tlsConnection, nil
	}
	return transport
}

type acceptedSettings struct {
	enabled     bool
	compression compressionSettings
}

func validateClientHandshakeResponse(response *http.Response, opts DialOptions) (acceptedSettings, error) {
	if len(response.Header.Values("Sec-WebSocket-Accept")) != 0 || len(response.Header.Values("Upgrade")) != 0 || len(response.Header.Values("Connection")) != 0 {
		return acceptedSettings{}, ErrHandshake
	}
	if encoding := strings.TrimSpace(response.Header.Get("Content-Encoding")); encoding != "" && !strings.EqualFold(encoding, "identity") {
		return acceptedSettings{}, ErrHandshake
	}
	selected := ""
	if values := response.Header.Values("Sec-WebSocket-Protocol"); len(values) != 0 {
		if len(values) != 1 || strings.Contains(values[0], ",") || !validToken(values[0]) {
			return acceptedSettings{}, ErrHandshake
		}
		selected = values[0]
	}
	if selected != "" {
		found := false
		for _, offered := range opts.Protocols {
			found = found || selected == offered
		}
		if !found {
			return acceptedSettings{}, ErrHandshake
		}
	}
	extensions := joinedHeader(response.Header, "Sec-WebSocket-Extensions")
	if opts.Compression == nil {
		if extensions != "" {
			return acceptedSettings{}, ErrInvalidExtension
		}
		return acceptedSettings{}, nil
	}
	enabled, compression, err := acceptCompressionResponse(extensions, *opts.Compression)
	return acceptedSettings{enabled: enabled, compression: compression}, err
}

type streamConn struct {
	reader           io.ReadCloser
	writer           io.WriteCloser
	cancel           context.CancelFunc
	onClose          func()
	setReadDeadline  func(time.Time) error
	setWriteDeadline func(time.Time) error
	close            sync.Once
	readMu           sync.Mutex
	writeMu          sync.Mutex
	readDeadline     deadlineState
	writeDeadline    deadlineState
}

type deadlineState struct {
	mu      sync.Mutex
	timer   *time.Timer
	expired atomic.Bool
}

func newStreamConn(reader io.ReadCloser, writer io.WriteCloser, cancel context.CancelFunc) *streamConn {
	return &streamConn{reader: reader, writer: writer, cancel: cancel}
}

func (c *streamConn) Read(payload []byte) (int, error) {
	c.readMu.Lock()
	defer c.readMu.Unlock()
	n, err := c.reader.Read(payload)
	if err != nil && c.readDeadline.expired.Load() {
		err = os.ErrDeadlineExceeded
	}
	return n, err
}

func (c *streamConn) Write(payload []byte) (int, error) {
	c.writeMu.Lock()
	defer c.writeMu.Unlock()
	n, err := c.writer.Write(payload)
	if err != nil && c.writeDeadline.expired.Load() {
		err = os.ErrDeadlineExceeded
	}
	return n, err
}

func (c *streamConn) Close() error {
	var closeErr error
	c.close.Do(func() {
		c.stopDeadline(&c.readDeadline)
		c.stopDeadline(&c.writeDeadline)
		writerErr := c.writer.Close()
		readerErr := c.reader.Close()
		c.cancel()
		closeErr = errors.Join(writerErr, readerErr)
		if c.onClose != nil {
			c.onClose()
		}
	})
	return closeErr
}

func (*streamConn) LocalAddr() net.Addr  { return streamAddr("http2-local") }
func (*streamConn) RemoteAddr() net.Addr { return streamAddr("http2-peer") }

func (c *streamConn) SetDeadline(deadline time.Time) error {
	if c.setReadDeadline != nil || c.setWriteDeadline != nil {
		var readErr, writeErr error
		if c.setReadDeadline != nil {
			readErr = c.setReadDeadline(deadline)
		}
		if c.setWriteDeadline != nil {
			writeErr = c.setWriteDeadline(deadline)
		}
		return errors.Join(readErr, writeErr)
	}
	c.setDeadline(&c.readDeadline, deadline)
	c.setDeadline(&c.writeDeadline, deadline)
	return nil
}

func (c *streamConn) SetReadDeadline(deadline time.Time) error {
	if c.setReadDeadline != nil {
		return c.setReadDeadline(deadline)
	}
	c.setDeadline(&c.readDeadline, deadline)
	return nil
}

func (c *streamConn) SetWriteDeadline(deadline time.Time) error {
	if c.setWriteDeadline != nil {
		return c.setWriteDeadline(deadline)
	}
	c.setDeadline(&c.writeDeadline, deadline)
	return nil
}

func (c *streamConn) setDeadline(state *deadlineState, deadline time.Time) {
	state.mu.Lock()
	defer state.mu.Unlock()
	if state.timer != nil {
		state.timer.Stop()
		state.timer = nil
	}
	state.expired.Store(false)
	if !deadline.IsZero() {
		delay := time.Until(deadline)
		if delay < 0 {
			delay = 0
		}
		state.timer = time.AfterFunc(delay, func() {
			state.expired.Store(true)
			c.cancel()
		})
	}
}

func (*streamConn) stopDeadline(state *deadlineState) {
	state.mu.Lock()
	defer state.mu.Unlock()
	if state.timer != nil {
		state.timer.Stop()
		state.timer = nil
	}
}

type streamAddr string

func (a streamAddr) Network() string { return "http2" }
func (a streamAddr) String() string  { return string(a) }

type responseStreamWriter struct {
	w       http.ResponseWriter
	flusher *http.ResponseController
}

func (w *responseStreamWriter) Write(payload []byte) (int, error) {
	n, err := w.w.Write(payload)
	if err == nil {
		err = w.flusher.Flush()
	}
	return n, err
}

func (*responseStreamWriter) Close() error { return nil }
