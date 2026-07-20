package websocket

import (
	"bytes"
	"context"
	"crypto/tls"
	"errors"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

func TestRFC8441EndToEnd(t *testing.T) {
	if !strings.Contains(os.Getenv("GODEBUG"), "http2xconnect=1") {
		t.Skip("requires GODEBUG=http2xconnect=1 at process start")
	}
	errCh := make(chan error, 1)
	server := httptest.NewUnstartedServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		conn, protocol, err := Upgrade(w, r, UpgradeOptions{
			Protocols:   []string{"chat.v2"},
			Compression: &CompressionOptions{},
		})
		if err != nil {
			errCh <- err
			return
		}
		defer conn.Close()
		if protocol != "chat.v2" || conn.HandshakeProtocol() != RFC8441Handshake {
			errCh <- errors.New("server did not negotiate RFC 8441")
			return
		}
		message, err := conn.ReadMessage()
		if err == nil {
			err = conn.WriteMessage(message)
		}
		errCh <- err
	}))
	server.EnableHTTP2 = true
	server.StartTLS()
	defer server.Close()

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	conn, response, err := Dial(ctx, "wss"+strings.TrimPrefix(server.URL, "https")+"/echo?transport=h2", DialOptions{
		Protocols:   []string{"chat.v2"},
		TLSConfig:   &tls.Config{InsecureSkipVerify: true}, // test server certificate
		Compression: &CompressionOptions{},
	})
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	if response.ProtoMajor != 2 || conn.HandshakeProtocol() != RFC8441Handshake {
		t.Fatalf("transport = HTTP/%d, %v", response.ProtoMajor, conn.HandshakeProtocol())
	}
	if response.Body != http.NoBody {
		t.Fatal("successful response exposed the HTTP/2 tunnel body")
	}
	payload := []byte("one API over an HTTP/2 stream")
	if err := conn.WriteText(payload); err != nil {
		t.Fatal(err)
	}
	message, err := conn.ReadMessage()
	if err != nil {
		t.Fatal(err)
	}
	text, ok := message.(TextMessage)
	if !ok || !bytes.Equal(text.Payload, payload) {
		t.Fatalf("echo = %#v", message)
	}
	if err := <-errCh; err != nil {
		t.Fatal(err)
	}
}

func TestRFC8441CleartextPriorKnowledge(t *testing.T) {
	if !strings.Contains(os.Getenv("GODEBUG"), "http2xconnect=1") {
		t.Skip("requires GODEBUG=http2xconnect=1 at process start")
	}
	server := httptest.NewUnstartedServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		conn, _, err := Upgrade(w, r, UpgradeOptions{})
		if err != nil {
			return
		}
		defer conn.Close()
		message, err := conn.ReadMessage()
		if err == nil {
			_ = conn.WriteMessage(message)
		}
	}))
	protocols := new(http.Protocols)
	protocols.SetUnencryptedHTTP2(true)
	server.Config.Protocols = protocols
	server.Start()
	defer server.Close()

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	conn, response, err := Dial(ctx, "ws"+strings.TrimPrefix(server.URL, "http"), DialOptions{HTTP2: HTTP2Only})
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	if response.ProtoMajor != 2 || conn.HandshakeProtocol() != RFC8441Handshake {
		t.Fatalf("transport = HTTP/%d, %v", response.ProtoMajor, conn.HandshakeProtocol())
	}
	if err := conn.WriteText([]byte("h2c")); err != nil {
		t.Fatal(err)
	}
	message, err := conn.ReadMessage()
	if err != nil {
		t.Fatal(err)
	}
	if text, ok := message.(TextMessage); !ok || string(text.Payload) != "h2c" {
		t.Fatalf("echo = %#v", message)
	}
}

func TestRFC8441OwnedTransportRejectsBadResponses(t *testing.T) {
	if !strings.Contains(os.Getenv("GODEBUG"), "http2xconnect=1") {
		t.Skip("requires GODEBUG=http2xconnect=1 at process start")
	}
	server := httptest.NewUnstartedServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		switch r.URL.Path {
		case "/status":
			w.WriteHeader(http.StatusNotFound)
		case "/header":
			w.Header().Set("Upgrade", "websocket")
			w.WriteHeader(http.StatusOK)
			_ = http.NewResponseController(w).Flush()
		}
	}))
	server.EnableHTTP2 = true
	server.StartTLS()
	defer server.Close()
	for _, path := range []string{"/status", "/header"} {
		_, response, err := Dial(context.Background(), "wss"+strings.TrimPrefix(server.URL, "https")+path, DialOptions{
			HTTP2:     HTTP2Only,
			TLSConfig: &tls.Config{InsecureSkipVerify: true}, // test server certificate
		})
		if !errors.Is(err, ErrHandshake) || response == nil {
			t.Fatalf("%s: response=%v error=%v", path, response, err)
		}
	}
}

func TestRFC8441DefaultTransportMultiplexesStreams(t *testing.T) {
	if !strings.Contains(os.Getenv("GODEBUG"), "http2xconnect=1") {
		t.Skip("requires GODEBUG=http2xconnect=1 at process start")
	}
	var tcpConnections atomic.Int32
	server := httptest.NewUnstartedServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		conn, _, err := Upgrade(w, r, UpgradeOptions{})
		if err != nil {
			return
		}
		defer conn.Close()
		message, err := conn.ReadMessage()
		if err == nil {
			_ = conn.WriteMessage(message)
		}
	}))
	server.EnableHTTP2 = true
	server.Config.ConnState = func(_ net.Conn, state http.ConnState) {
		if state == http.StateNew {
			tcpConnections.Add(1)
		}
	}
	server.StartTLS()
	defer server.Close()

	original := defaultSecureHTTP2Transport
	shared := newHTTP2Transport(DialOptions{TLSConfig: &tls.Config{InsecureSkipVerify: true}}, false)
	defaultSecureHTTP2Transport = shared
	defer func() {
		shared.CloseIdleConnections()
		defaultSecureHTTP2Transport = original
	}()
	url := "wss" + strings.TrimPrefix(server.URL, "https")
	first, _, err := Dial(context.Background(), url, DialOptions{})
	if err != nil {
		t.Fatal(err)
	}
	defer first.Close()
	second, _, err := Dial(context.Background(), url, DialOptions{})
	if err != nil {
		t.Fatal(err)
	}
	defer second.Close()
	for i, conn := range []*Conn{first, second} {
		payload := []byte{byte(i + 1)}
		if err := conn.WriteBinary(payload); err != nil {
			t.Fatal(err)
		}
		message, err := conn.ReadMessage()
		if err != nil {
			t.Fatal(err)
		}
		if binary, ok := message.(BinaryMessage); !ok || !bytes.Equal(binary.Payload, payload) {
			t.Fatalf("stream %d echo = %#v", i, message)
		}
	}
	if got := tcpConnections.Load(); got != 1 {
		t.Fatalf("two WebSockets used %d TCP connections", got)
	}
}

func TestDialAutomaticallyFallsBackToRFC6455(t *testing.T) {
	server := httptest.NewUnstartedServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		conn, _, err := Upgrade(w, r, UpgradeOptions{})
		if err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		defer conn.Close()
		message, err := conn.ReadMessage()
		if err == nil {
			_ = conn.WriteMessage(message)
		}
	}))
	server.EnableHTTP2 = false
	server.StartTLS()
	defer server.Close()

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	conn, response, err := Dial(ctx, "wss"+strings.TrimPrefix(server.URL, "https"), DialOptions{
		TLSConfig: &tls.Config{InsecureSkipVerify: true}, // test server certificate
	})
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	if response.ProtoMajor != 1 || conn.HandshakeProtocol() != RFC6455Handshake {
		t.Fatalf("fallback transport = HTTP/%d, %v", response.ProtoMajor, conn.HandshakeProtocol())
	}
	if err := conn.WriteBinary([]byte{1, 2, 3}); err != nil {
		t.Fatal(err)
	}
	message, err := conn.ReadMessage()
	if err != nil {
		t.Fatal(err)
	}
	if binary, ok := message.(BinaryMessage); !ok || !bytes.Equal(binary.Payload, []byte{1, 2, 3}) {
		t.Fatalf("echo = %#v", message)
	}
}

func TestDialFallsBackAfterHTTP2UnsupportedStatus(t *testing.T) {
	if !strings.Contains(os.Getenv("GODEBUG"), "http2xconnect=1") {
		t.Skip("requires GODEBUG=http2xconnect=1 at process start")
	}
	server := httptest.NewUnstartedServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.ProtoMajor == 2 {
			http.NotFound(w, r)
			return
		}
		conn, _, err := Upgrade(w, r, UpgradeOptions{})
		if err != nil {
			return
		}
		_ = conn.Close()
	}))
	server.EnableHTTP2 = true
	server.StartTLS()
	defer server.Close()
	conn, response, err := Dial(context.Background(), "wss"+strings.TrimPrefix(server.URL, "https"), DialOptions{
		TLSConfig: &tls.Config{InsecureSkipVerify: true}, // test server certificate
	})
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	if response.ProtoMajor != 1 || conn.HandshakeProtocol() != RFC6455Handshake {
		t.Fatalf("fallback transport = HTTP/%d, %v", response.ProtoMajor, conn.HandshakeProtocol())
	}
}

type roundTripFunc func(*http.Request) (*http.Response, error)

func (f roundTripFunc) RoundTrip(r *http.Request) (*http.Response, error) { return f(r) }

func TestRFC8441ClientHandshakeValidation(t *testing.T) {
	for name, mutate := range map[string]func(*http.Response){
		"wrong protocol": func(r *http.Response) { r.ProtoMajor = 1 },
		"wrong status":   func(r *http.Response) { r.StatusCode = http.StatusUnauthorized },
		"accept key":     func(r *http.Response) { r.Header.Set("Sec-WebSocket-Accept", "forbidden") },
		"upgrade":        func(r *http.Response) { r.Header.Set("Upgrade", "websocket") },
		"connection":     func(r *http.Response) { r.Header.Set("Connection", "upgrade") },
		"content coding": func(r *http.Response) { r.Header.Set("Content-Encoding", "gzip") },
		"protocol list":  func(r *http.Response) { r.Header.Set("Sec-WebSocket-Protocol", "one, two") },
		"unsolicited":    func(r *http.Response) { r.Header.Set("Sec-WebSocket-Protocol", "other") },
		"extension":      func(r *http.Response) { r.Header.Set("Sec-WebSocket-Extensions", "unknown") },
	} {
		t.Run(name, func(t *testing.T) {
			transport := roundTripFunc(func(request *http.Request) (*http.Response, error) {
				if request.Method != http.MethodConnect || request.Header.Get(":protocol") != "websocket" || request.Header.Get("Sec-WebSocket-Key") != "" || request.Header.Get("Accept-Encoding") != "identity" {
					t.Fatal("invalid extended CONNECT request")
				}
				response := &http.Response{StatusCode: http.StatusOK, ProtoMajor: 2, ProtoMinor: 0, Header: make(http.Header), Body: io.NopCloser(strings.NewReader(""))}
				mutate(response)
				return response, nil
			})
			_, _, err := Dial(context.Background(), "wss://example.test/socket", DialOptions{HTTP2: HTTP2Only, Protocols: []string{"one"}, HTTP2Transport: transport})
			if err == nil {
				t.Fatal("invalid response accepted")
			}
		})
	}
}

func TestRFC8441ClientOpeningErrors(t *testing.T) {
	called := false
	transport := roundTripFunc(func(*http.Request) (*http.Response, error) {
		called = true
		return nil, errors.New("unexpected round trip")
	})
	for name, rawURL := range map[string]string{
		"parse":    ":%",
		"scheme":   "ftp://example.test/socket",
		"host":     "wss:///socket",
		"fragment": "wss://example.test/socket#fragment",
	} {
		t.Run(name, func(t *testing.T) {
			if _, _, err := Dial(context.Background(), rawURL, DialOptions{HTTP2: HTTP2Only, HTTP2Transport: transport}); err == nil {
				t.Fatal("invalid URL accepted")
			}
		})
	}
	for _, options := range []DialOptions{
		{HTTP2: HTTP2Only, HTTP2Transport: transport, Protocols: []string{"bad protocol"}},
		{HTTP2: HTTP2Only, HTTP2Transport: transport, Protocols: []string{"same", "same"}},
		{HTTP2: HTTP2Only, HTTP2Transport: transport, Compression: &CompressionOptions{ClientMaxWindowBits: 7}},
	} {
		if _, _, err := Dial(context.Background(), "wss://example.test/socket", options); err == nil {
			t.Fatal("invalid options accepted")
		}
	}
	for _, forbidden := range []string{"Connection", "Upgrade", "Host", "Sec-WebSocket-Key", "Sec-WebSocket-Accept", ":protocol"} {
		header := make(http.Header)
		header.Set(forbidden, "forbidden")
		if _, _, err := Dial(context.Background(), "wss://example.test/socket", DialOptions{HTTP2: HTTP2Only, HTTP2Transport: transport, Header: header}); err == nil {
			t.Fatalf("accepted forbidden %s", forbidden)
		}
	}
	if called {
		t.Fatal("transport called for invalid input")
	}
}

func TestRFC8441TransportAndCancellationErrors(t *testing.T) {
	want := errors.New("round trip failed")
	wrapped := &http2UnavailableError{cause: want}
	if wrapped.Error() != want.Error() || !errors.Is(wrapped, want) || isHTTP2Unavailable(nil) {
		t.Fatal("HTTP/2 availability error contract failed")
	}
	transport := roundTripFunc(func(*http.Request) (*http.Response, error) { return nil, want })
	if _, _, err := Dial(context.Background(), "wss://example.test", DialOptions{HTTP2: HTTP2Only, HTTP2Transport: transport}); !errors.Is(err, want) {
		t.Fatalf("round trip error = %v", err)
	}
	if _, _, err := Dial(context.Background(), "wss://example.test", DialOptions{HTTP2Transport: transport}); !errors.Is(err, want) {
		t.Fatalf("automatic mode hid transport error = %v", err)
	}

	ctx, cancel := context.WithCancel(context.Background())
	transport = roundTripFunc(func(*http.Request) (*http.Response, error) {
		cancel()
		return &http.Response{StatusCode: http.StatusOK, ProtoMajor: 2, Header: make(http.Header), Body: io.NopCloser(strings.NewReader(""))}, nil
	})
	if _, _, err := Dial(ctx, "wss://example.test", DialOptions{HTTP2: HTTP2Only, HTTP2Transport: transport}); !errors.Is(err, context.Canceled) {
		t.Fatalf("cancellation error = %v", err)
	}

	want = errors.New("dial failed")
	if _, _, err := Dial(context.Background(), "wss://example.test", DialOptions{
		HTTP2: HTTP2Only,
		DialContext: func(context.Context, string, string) (net.Conn, error) {
			return nil, want
		},
	}); !errors.Is(err, want) {
		t.Fatalf("dial error = %v", err)
	}

	client, peer := net.Pipe()
	_ = peer.Close()
	if _, _, err := Dial(context.Background(), "wss://example.test", DialOptions{
		HTTP2: HTTP2Only,
		DialContext: func(context.Context, string, string) (net.Conn, error) {
			return client, nil
		},
	}); err == nil {
		t.Fatal("TLS handshake failure accepted")
	}
	var address string
	if _, _, err := dialRFC6455(context.Background(), "wss://example.test/socket", DialOptions{
		DialContext: func(_ context.Context, _, target string) (net.Conn, error) {
			address = target
			return nil, want
		},
	}); !errors.Is(err, want) || address != "example.test:443" {
		t.Fatalf("RFC 6455 secure default address = %q, %v", address, err)
	}
}

type bufferWriteCloser struct {
	bytes.Buffer
	closed bool
}

func (w *bufferWriteCloser) Close() error { w.closed = true; return nil }

type errorWriteCloser struct{ err error }

func (w errorWriteCloser) Write([]byte) (int, error) { return 0, w.err }
func (errorWriteCloser) Close() error                { return nil }

func TestRFC8441StreamConnectionContract(t *testing.T) {
	reader := io.NopCloser(strings.NewReader("input"))
	writer := new(bufferWriteCloser)
	canceled := make(chan struct{})
	var cancelOnce sync.Once
	stream := newStreamConn(reader, writer, func() { cancelOnce.Do(func() { close(canceled) }) })
	if stream.LocalAddr().Network() != "http2" || stream.LocalAddr().String() != "http2-local" || stream.RemoteAddr().String() != "http2-peer" {
		t.Fatalf("addresses = %v %v", stream.LocalAddr(), stream.RemoteAddr())
	}
	buffer := make([]byte, 5)
	if _, err := io.ReadFull(stream, buffer); err != nil || string(buffer) != "input" {
		t.Fatalf("read = %q, %v", buffer, err)
	}
	if _, err := stream.Write([]byte("output")); err != nil || writer.String() != "output" {
		t.Fatalf("write = %q, %v", writer.String(), err)
	}
	if err := stream.SetDeadline(time.Now().Add(time.Hour)); err != nil {
		t.Fatal(err)
	}
	if err := stream.SetDeadline(time.Time{}); err != nil {
		t.Fatal(err)
	}
	if err := stream.SetReadDeadline(time.Now().Add(-time.Second)); err != nil {
		t.Fatal(err)
	}
	select {
	case <-canceled:
	case <-time.After(time.Second):
		t.Fatal("deadline did not cancel stream")
	}
	if _, err := stream.Read(make([]byte, 1)); !errors.Is(err, os.ErrDeadlineExceeded) {
		t.Fatalf("expired read = %v", err)
	}
	if err := stream.Close(); err != nil || !writer.closed {
		t.Fatalf("close = %v, writer closed=%v", err, writer.closed)
	}
	if err := stream.Close(); err != nil {
		t.Fatalf("second close = %v", err)
	}

	writeCanceled := make(chan struct{})
	var writeCancelOnce sync.Once
	writeStream := newStreamConn(io.NopCloser(strings.NewReader("")), errorWriteCloser{err: errors.New("write")}, func() {
		writeCancelOnce.Do(func() { close(writeCanceled) })
	})
	if err := writeStream.SetWriteDeadline(time.Now().Add(-time.Second)); err != nil {
		t.Fatal(err)
	}
	<-writeCanceled
	if _, err := writeStream.Write([]byte("x")); !errors.Is(err, os.ErrDeadlineExceeded) {
		t.Fatalf("expired write = %v", err)
	}
	_ = writeStream.Close()
}

func TestRFC8441ServerDeadlines(t *testing.T) {
	stream := newStreamConn(io.NopCloser(strings.NewReader("")), new(bufferWriteCloser), func() {})
	wantRead, wantWrite := errors.New("read deadline"), errors.New("write deadline")
	stream.setReadDeadline = func(time.Time) error { return wantRead }
	stream.setWriteDeadline = func(time.Time) error { return wantWrite }
	if err := stream.SetReadDeadline(time.Now()); !errors.Is(err, wantRead) {
		t.Fatalf("read deadline = %v", err)
	}
	if err := stream.SetWriteDeadline(time.Now()); !errors.Is(err, wantWrite) {
		t.Fatalf("write deadline = %v", err)
	}
	if err := stream.SetDeadline(time.Now()); !errors.Is(err, wantRead) || !errors.Is(err, wantWrite) {
		t.Fatalf("combined deadline = %v", err)
	}
}

func TestHandshakeProtocolString(t *testing.T) {
	if RFC6455Handshake.String() != "RFC 6455" || RFC8441Handshake.String() != "RFC 8441" {
		t.Fatalf("strings = %q, %q", RFC6455Handshake, RFC8441Handshake)
	}
	if !IsRFC8441Request(&http.Request{Method: http.MethodConnect, ProtoMajor: 2, Header: http.Header{":protocol": {"websocket"}}}) || IsRFC8441Request(nil) {
		t.Fatal("RFC 8441 request classification failed")
	}
	if shouldTryHTTP2(&url.URL{Scheme: "wss"}, DialOptions{HTTP2: HTTP1Only, HTTP2Transport: roundTripFunc(nil)}) {
		t.Fatal("HTTP1Only did not disable RFC 8441")
	}
}

type recordingResponseWriter struct {
	header http.Header
	status int
	body   bytes.Buffer
	mu     sync.Mutex
}

func (w *recordingResponseWriter) Header() http.Header { return w.header }
func (w *recordingResponseWriter) WriteHeader(status int) {
	w.status = status
}
func (w *recordingResponseWriter) Write(payload []byte) (int, error) {
	w.mu.Lock()
	defer w.mu.Unlock()
	return w.body.Write(payload)
}
func (*recordingResponseWriter) Flush() {}

type failingFlushWriter struct {
	*recordingResponseWriter
	err error
}

func (w *failingFlushWriter) FlushError() error { return w.err }

func TestRFC8441ServerHandshake(t *testing.T) {
	request := httptest.NewRequest(http.MethodConnect, "https://example.test/socket", nil)
	request.Proto = "HTTP/2.0"
	request.ProtoMajor = 2
	request.ProtoMinor = 0
	request.Header.Set(":protocol", "websocket")
	request.Header.Set("Sec-WebSocket-Version", "13")
	request.Header.Set("Sec-WebSocket-Protocol", "other, chat.v2")
	request.Header.Set("Sec-WebSocket-Extensions", "permessage-deflate; client_no_context_takeover")
	request.Body = io.NopCloser(strings.NewReader(""))
	w := &recordingResponseWriter{header: make(http.Header)}
	conn, protocol, err := Upgrade(w, request, UpgradeOptions{Protocols: []string{"chat.v2"}, Compression: &CompressionOptions{}})
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	if w.status != http.StatusOK || protocol != "chat.v2" || conn.HandshakeProtocol() != RFC8441Handshake {
		t.Fatalf("status=%d protocol=%q handshake=%v", w.status, protocol, conn.HandshakeProtocol())
	}
	if w.header.Get("Sec-WebSocket-Accept") != "" || w.header.Get("Sec-WebSocket-Protocol") != "chat.v2" || w.header.Get("Sec-WebSocket-Extensions") == "" {
		t.Fatalf("response headers = %#v", w.header)
	}
}

func TestRFC8441ServerRejectsMalformedRequests(t *testing.T) {
	base := func() *http.Request {
		request := httptest.NewRequest(http.MethodConnect, "https://example.test/socket", nil)
		request.Proto = "HTTP/2.0"
		request.ProtoMajor = 2
		request.ProtoMinor = 0
		request.Header.Set(":protocol", "websocket")
		request.Header.Set("Sec-WebSocket-Version", "13")
		return request
	}
	for name, mutate := range map[string]func(*http.Request){
		"method":       func(r *http.Request) { r.Method = http.MethodGet },
		"protocol":     func(r *http.Request) { r.Header.Set(":protocol", "other") },
		"host":         func(r *http.Request) { r.Host = "" },
		"version":      func(r *http.Request) { r.Header.Set("Sec-WebSocket-Version", "12") },
		"connection":   func(r *http.Request) { r.Header.Set("Connection", "upgrade") },
		"upgrade":      func(r *http.Request) { r.Header.Set("Upgrade", "websocket") },
		"key":          func(r *http.Request) { r.Header.Set("Sec-WebSocket-Key", "key") },
		"accept":       func(r *http.Request) { r.Header.Set("Sec-WebSocket-Accept", "accept") },
		"bad subproto": func(r *http.Request) { r.Header.Set("Sec-WebSocket-Protocol", "bad protocol") },
	} {
		t.Run(name, func(t *testing.T) {
			request := base()
			mutate(request)
			w := &recordingResponseWriter{header: make(http.Header)}
			if _, _, err := Upgrade(w, request, UpgradeOptions{}); err == nil {
				t.Fatal("malformed request accepted")
			}
		})
	}
}

func TestRFC8441ServerPolicyAndFlushErrors(t *testing.T) {
	request := func() *http.Request {
		r := httptest.NewRequest(http.MethodConnect, "https://example.test/socket", nil)
		r.Proto, r.ProtoMajor, r.ProtoMinor = "HTTP/2.0", 2, 0
		r.Header.Set(":protocol", "websocket")
		r.Header.Set("Sec-WebSocket-Version", "13")
		return r
	}
	w := &recordingResponseWriter{header: make(http.Header)}
	if _, _, err := Upgrade(w, request(), UpgradeOptions{CheckOrigin: func(*http.Request) bool { return false }}); !errors.Is(err, ErrHandshake) {
		t.Fatalf("origin error = %v", err)
	}
	if _, _, err := Upgrade(w, request(), UpgradeOptions{Compression: &CompressionOptions{ServerMaxWindowBits: 7}}); !errors.Is(err, ErrInvalidExtension) {
		t.Fatalf("compression error = %v", err)
	}
	want := errors.New("flush failed")
	failing := &failingFlushWriter{recordingResponseWriter: &recordingResponseWriter{header: make(http.Header)}, err: want}
	if _, _, err := Upgrade(failing, request(), UpgradeOptions{}); !errors.Is(err, want) {
		t.Fatalf("flush error = %v", err)
	}
}
