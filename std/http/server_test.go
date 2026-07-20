package http

import (
	"context"
	"crypto/tls"
	"errors"
	"io"
	"net"
	nethttp "net/http"
	"net/http/httptest"
	"sync/atomic"
	"testing"
	"time"

	"github.com/quic-go/quic-go"
)

func TestServerServesOneHandlerOverHTTP2AndHTTP3(t *testing.T) {
	seed := httptest.NewTLSServer(nethttp.NotFoundHandler())
	serverTLS := seed.TLS.Clone()
	seed.Close()
	var negotiatedQUIC atomic.Uint32
	serverTLS.GetConfigForClient = func(hello *tls.ClientHelloInfo) (*tls.Config, error) {
		if version, ok := hello.Context().Value(quic.QUICVersionContextKey).(quic.Version); ok {
			negotiatedQUIC.Store(uint32(version))
		}
		return nil, nil
	}
	tcp, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	udp, err := net.ListenPacket("udp", "127.0.0.1:0")
	if err != nil {
		tcp.Close()
		t.Fatal(err)
	}
	server := &Server{
		TLSConfig: serverTLS,
		// A successful default request against a v2-only server proves that
		// RFC 9369 is enabled without custom HTTP/3 wiring.
		QUICConfig: &quic.Config{Versions: []quic.Version{quic.Version2}},
		Handler: nethttp.HandlerFunc(func(w nethttp.ResponseWriter, r *nethttp.Request) {
			_, _ = io.WriteString(w, r.Proto)
		}),
	}
	done := make(chan error, 1)
	go func() { done <- server.Serve(tcp, udp) }()
	defer func() {
		ctx, cancel := context.WithTimeout(context.Background(), time.Second)
		defer cancel()
		_ = server.Shutdown(ctx)
		select {
		case err := <-done:
			if err != nil && !errors.Is(err, nethttp.ErrServerClosed) {
				t.Errorf("Serve: %v", err)
			}
		case <-ctx.Done():
			t.Error("server did not stop")
		}
	}()
	fallback := &nethttp.Transport{
		TLSClientConfig:   &tls.Config{InsecureSkipVerify: true},
		ForceAttemptHTTP2: true,
	}
	clientProtocols := new(nethttp.Protocols)
	clientProtocols.SetHTTP1(true)
	clientProtocols.SetHTTP2(true)
	fallback.Protocols = clientProtocols
	transport := &Transport{
		TLSClientConfig: &tls.Config{InsecureSkipVerify: true},
		Fallback:        fallback,
	}
	defer transport.CloseIdleConnections()
	client := &nethttp.Client{Transport: transport}
	url := "https://" + tcp.Addr().String()
	first, err := client.Get(url)
	if err != nil {
		t.Fatal(err)
	}
	firstBody, _ := io.ReadAll(first.Body)
	first.Body.Close()
	if first.ProtoMajor != 2 || string(firstBody) != "HTTP/2.0" {
		t.Fatalf("first = HTTP/%d %q, ALPN=%q", first.ProtoMajor, firstBody, first.TLS.NegotiatedProtocol)
	}
	second, err := client.Get(url)
	if err != nil {
		t.Fatal(err)
	}
	secondBody, _ := io.ReadAll(second.Body)
	second.Body.Close()
	if second.ProtoMajor != 3 || string(secondBody) != "HTTP/3.0" {
		t.Fatalf("second = HTTP/%d %q", second.ProtoMajor, secondBody)
	}
	if got := quic.Version(negotiatedQUIC.Load()); got != quic.Version2 {
		t.Fatalf("negotiated QUIC version = %#x, want RFC 9369 v2", got)
	}
}

func TestDefaultClientUsesAutomaticTransport(t *testing.T) {
	if DefaultClient.Transport != DefaultTransport {
		t.Fatalf("DefaultClient.Transport = %T, want shared *Transport", DefaultClient.Transport)
	}
	if DefaultTransport.Mode != Auto || DefaultTransport.PriorKnowledge {
		t.Fatalf("default transport = mode %v, prior knowledge %v", DefaultTransport.Mode, DefaultTransport.PriorKnowledge)
	}
}

func TestPackageGetWorksWithoutClientSetup(t *testing.T) {
	server := httptest.NewServer(nethttp.HandlerFunc(func(w nethttp.ResponseWriter, _ *nethttp.Request) {
		_, _ = io.WriteString(w, "ready")
	}))
	defer server.Close()
	response, err := Get(server.URL)
	if err != nil {
		t.Fatal(err)
	}
	defer response.Body.Close()
	body, err := io.ReadAll(response.Body)
	if err != nil || string(body) != "ready" {
		t.Fatalf("body = %q, %v", body, err)
	}
}
