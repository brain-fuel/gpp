package websocket

import (
	"bufio"
	"context"
	"crypto/rand"
	"crypto/tls"
	"encoding/base64"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"strings"
	"time"
)

type DialOptions struct {
	Protocols []string
	Header    http.Header
	TLSConfig *tls.Config
	NetDialer *net.Dialer
	// DialContext overrides TCP connection establishment, enabling proxies,
	// custom transports, and deterministic fault injection.
	DialContext func(context.Context, string, string) (net.Conn, error)
	Config      ConnConfig
	Compression *CompressionOptions
	// HTTP2 controls RFC 8441 extended CONNECT. Auto prefers HTTP/2 for wss
	// URLs and transparently falls back to RFC 6455. Cleartext ws remains on
	// HTTP/1.1 unless HTTP2Only is selected.
	HTTP2 HTTP2Mode
	// HTTP2Transport optionally supplies a shared HTTP/2-capable transport.
	// It must preserve a streaming request body and response body.
	HTTP2Transport http.RoundTripper
}

// Dial opens a WebSocket using RFC 8441 when selected and RFC 6455 otherwise.
// On success the returned response is metadata only; Conn exclusively owns the
// underlying transport stream, so callers may safely ignore response.Body.
func Dial(ctx context.Context, rawURL string, opts DialOptions) (*Conn, *http.Response, error) {
	return dial(ctx, rawURL, opts)
}

func dialRFC6455(ctx context.Context, rawURL string, opts DialOptions) (*Conn, *http.Response, error) {
	seenProtocols := make(map[string]struct{}, len(opts.Protocols))
	for _, protocol := range opts.Protocols {
		if !validToken(protocol) {
			return nil, nil, ErrHandshake
		}
		if _, duplicate := seenProtocols[protocol]; duplicate {
			return nil, nil, ErrHandshake
		}
		seenProtocols[protocol] = struct{}{}
	}
	var compressionHeader string
	if opts.Compression != nil {
		var err error
		compressionHeader, err = compressionOffer(*opts.Compression)
		if err != nil {
			return nil, nil, err
		}
	}
	u, err := url.Parse(rawURL)
	if err != nil {
		return nil, nil, err
	}
	if u.Scheme != "ws" && u.Scheme != "wss" {
		return nil, nil, fmt.Errorf("websocket: unsupported scheme %q", u.Scheme)
	}
	if u.Hostname() == "" || u.Fragment != "" {
		return nil, nil, ErrHandshake
	}
	host := u.Hostname()
	port := u.Port()
	if port == "" {
		if u.Scheme == "wss" {
			port = "443"
		} else {
			port = "80"
		}
	}
	address := net.JoinHostPort(host, port)
	d := opts.NetDialer
	if d == nil {
		d = &net.Dialer{Timeout: 30 * time.Second, KeepAlive: 30 * time.Second}
	}
	dial := d.DialContext
	if opts.DialContext != nil {
		dial = opts.DialContext
	}
	nc, err := dial(ctx, "tcp", address)
	if err != nil {
		return nil, nil, err
	}
	if u.Scheme == "wss" {
		cfg := opts.TLSConfig
		if cfg == nil {
			cfg = &tls.Config{ServerName: u.Hostname(), MinVersion: tls.VersionTLS12}
		} else {
			cfg = cfg.Clone()
			if cfg.ServerName == "" {
				cfg.ServerName = u.Hostname()
			}
		}
		tlsConn := tls.Client(nc, cfg)
		if err = tlsConn.HandshakeContext(ctx); err != nil {
			_ = nc.Close()
			return nil, nil, err
		}
		nc = tlsConn
	}
	fail := true
	defer func() {
		if fail {
			_ = nc.Close()
		}
	}()
	stopCancellation := context.AfterFunc(ctx, func() { _ = nc.Close() })
	defer stopCancellation()
	if deadline, ok := ctx.Deadline(); ok {
		_ = nc.SetDeadline(deadline)
	}
	var nonce [16]byte
	if _, err = io.ReadFull(rand.Reader, nonce[:]); err != nil {
		return nil, nil, err
	}
	key := base64.StdEncoding.EncodeToString(nonce[:])
	path := u.Path
	if path == "" {
		path = "/"
	}
	head := opts.Header.Clone()
	if head == nil {
		head = make(http.Header)
	}
	head.Set("Host", u.Host)
	head.Set("Upgrade", "websocket")
	head.Set("Connection", "Upgrade")
	head.Set("Sec-WebSocket-Key", key)
	head.Set("Sec-WebSocket-Version", "13")
	if len(opts.Protocols) > 0 {
		head.Set("Sec-WebSocket-Protocol", strings.Join(opts.Protocols, ", "))
	}
	if opts.Compression != nil {
		head.Set("Sec-WebSocket-Extensions", compressionHeader)
	}
	reqURL := &url.URL{Path: path, RawPath: u.RawPath, RawQuery: u.RawQuery}
	req := &http.Request{Method: http.MethodGet, URL: reqURL, Host: u.Host, Header: head, ProtoMajor: 1, ProtoMinor: 1}
	if err = req.Write(nc); err != nil {
		return nil, nil, err
	}
	br := bufio.NewReaderSize(nc, 4096)
	resp, err := http.ReadResponse(br, req)
	if err != nil {
		return nil, nil, err
	}
	accept, singleAccept := singleHeader(resp.Header, "Sec-WebSocket-Accept")
	if resp.ProtoMajor != 1 || resp.ProtoMinor < 1 || resp.StatusCode != http.StatusSwitchingProtocols || !hasToken(joinedHeader(resp.Header, "Connection"), "upgrade") || !hasToken(joinedHeader(resp.Header, "Upgrade"), "websocket") || !singleAccept || accept != AcceptKey(key) {
		return nil, resp, ErrHandshake
	}
	selected := ""
	if values := resp.Header.Values("Sec-WebSocket-Protocol"); len(values) > 0 {
		if len(values) != 1 || strings.Contains(values[0], ",") || !validToken(values[0]) {
			return nil, resp, ErrHandshake
		}
		selected = values[0]
	}
	if selected != "" {
		ok := false
		for _, p := range opts.Protocols {
			if selected == p {
				ok = true
				break
			}
		}
		if !ok {
			return nil, resp, ErrHandshake
		}
	}
	responseExtensions := joinedHeader(resp.Header, "Sec-WebSocket-Extensions")
	compressed, settings := false, compressionSettings{}
	if opts.Compression == nil {
		if responseExtensions != "" {
			return nil, resp, ErrInvalidExtension
		}
	} else {
		compressed, settings, err = acceptCompressionResponse(responseExtensions, *opts.Compression)
		if err != nil {
			return nil, resp, err
		}
	}
	conn := NewConn(nc, ClientSide, br, opts.Config)
	if compressed {
		conn.enableCompression(settings)
	}
	stopped := stopCancellation()
	if !stopped || ctx.Err() != nil {
		return nil, resp, ctx.Err()
	}
	_ = nc.SetDeadline(time.Time{})
	fail = false
	return conn, resp, nil
}
