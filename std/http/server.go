package http

import (
	"context"
	"crypto/tls"
	"errors"
	"fmt"
	"net"
	nethttp "net/http"
	"strconv"
	"sync"

	"github.com/quic-go/quic-go"
	refhttp3 "github.com/quic-go/quic-go/http3"
	nativehttp3 "goforge.dev/goplus/std/http3"
)

// Server serves one net/http Handler over HTTP/3 and TLS-based HTTP/2 or
// HTTP/1.1. The zero value requires TLSConfig to be set before Serve.
type Server struct {
	Handler          nethttp.Handler
	TLSConfig        *tls.Config
	QUICConfig       *quic.Config
	NativeQUICConfig *nativehttp3.RFC9000Config
	// XQUICConfig is retained for compatibility. NativeQUICConfig takes
	// precedence when both are set.
	// Deprecated: use NativeQUICConfig.
	XQUICConfig *nativehttp3.RFC9000Config

	HTTP *nethttp.Server
	// NativeHTTP3 opts into and customizes the experimental native server.
	// When both HTTP3 and NativeHTTP3 are nil, the RFC 9368/9369-capable
	// quic-go server is used so QUIC v1 and v2 work out of the box.
	NativeHTTP3 *nativehttp3.NativeServer
	// HTTP3 customizes the default quic-go server.
	HTTP3 *refhttp3.Server

	mu     sync.Mutex
	tcp    net.Listener
	udp    net.PacketConn
	closed bool
}

// Serve serves TLS/TCP on tcp and QUIC on udp until either server fails or
// Shutdown is called. It advertises the UDP port in Alt-Svc on TCP responses.
// Serve owns and closes both listeners.
func (s *Server) Serve(tcp net.Listener, udp net.PacketConn) error {
	if tcp == nil || udp == nil {
		return errors.New("http: both TCP and UDP listeners are required")
	}
	if s.TLSConfig == nil || len(s.TLSConfig.Certificates) == 0 && s.TLSConfig.GetCertificate == nil {
		return errors.New("http: TLSConfig with a server certificate is required")
	}
	s.mu.Lock()
	if s.closed {
		s.mu.Unlock()
		return nethttp.ErrServerClosed
	}
	s.tcp, s.udp = tcp, udp
	s.mu.Unlock()

	handler := s.Handler
	if handler == nil {
		handler = nethttp.DefaultServeMux
	}
	_, udpPort, err := net.SplitHostPort(udp.LocalAddr().String())
	if err != nil {
		return err
	}
	port, err := strconv.Atoi(udpPort)
	if err != nil {
		return err
	}
	var serveHTTP3 func(net.PacketConn) error
	if s.NativeHTTP3 == nil {
		h3server := s.HTTP3
		if h3server == nil {
			h3server = new(refhttp3.Server)
			s.HTTP3 = h3server
		}
		if h3server.TLSConfig == nil {
			h3server.TLSConfig = s.TLSConfig.Clone()
		}
		if h3server.QUICConfig == nil && s.QUICConfig != nil {
			h3server.QUICConfig = s.QUICConfig.Clone()
		}
		h3server.Port = port
		h3server.Handler = handler
		serveHTTP3 = h3server.Serve
	} else {
		h3server := s.NativeHTTP3
		if h3server.TLSConfig == nil {
			h3server.TLSConfig = s.TLSConfig.Clone()
		}
		if h3server.QUICConfig == nil {
			config := s.NativeQUICConfig
			if config == nil {
				config = s.XQUICConfig
			}
			if config != nil {
				h3server.QUICConfig = config.Clone()
			}
		}
		h3server.Handler = handler
		serveHTTP3 = h3server.Serve
	}

	tcpHandler := nethttp.HandlerFunc(func(w nethttp.ResponseWriter, r *nethttp.Request) {
		w.Header().Add("Alt-Svc", fmt.Sprintf(`h3=":%d"; ma=2592000`, port))
		handler.ServeHTTP(w, r)
	})
	httpServer := s.HTTP
	if httpServer == nil {
		httpServer = new(nethttp.Server)
		s.HTTP = httpServer
	}
	if httpServer.Handler == nil {
		httpServer.Handler = tcpHandler
	}
	if httpServer.TLSConfig == nil {
		httpServer.TLSConfig = s.TLSConfig.Clone()
		// Let net/http derive the HTTP ALPN order from Protocols. Certificate
		// configs copied from another server can otherwise pin http/1.1 first.
		httpServer.TLSConfig.NextProtos = nil
	}
	if httpServer.Protocols == nil {
		protocols := new(nethttp.Protocols)
		protocols.SetHTTP1(true)
		protocols.SetHTTP2(true)
		httpServer.Protocols = protocols
	}

	errs := make(chan error, 2)
	go func() { errs <- serveHTTP3(udp) }()
	go func() { errs <- httpServer.ServeTLS(tcp, "", "") }()
	err = <-errs
	_ = s.Close()
	second := <-errs
	if benignServerError(err) {
		err = second
	}
	if benignServerError(err) {
		return nethttp.ErrServerClosed
	}
	return err
}

func benignServerError(err error) bool {
	return err == nil || errors.Is(err, nethttp.ErrServerClosed) || errors.Is(err, net.ErrClosed)
}

// Shutdown gracefully shuts down both protocol families.
func (s *Server) Shutdown(ctx context.Context) error {
	s.mu.Lock()
	s.closed = true
	httpServer, h3server, nativeServer := s.HTTP, s.HTTP3, s.NativeHTTP3
	s.mu.Unlock()
	var errs []error
	if h3server != nil {
		if err := h3server.Shutdown(ctx); err != nil && !benignServerError(err) {
			errs = append(errs, err)
		}
	}
	if nativeServer != nil {
		if err := nativeServer.Shutdown(ctx); err != nil && !benignServerError(err) {
			errs = append(errs, err)
		}
	}
	if httpServer != nil {
		if err := httpServer.Shutdown(ctx); err != nil && !benignServerError(err) {
			errs = append(errs, err)
		}
	}
	return errors.Join(errs...)
}

// Close immediately closes servers and their listeners.
func (s *Server) Close() error {
	s.mu.Lock()
	s.closed = true
	httpServer, h3server, nativeServer, tcp, udp := s.HTTP, s.HTTP3, s.NativeHTTP3, s.tcp, s.udp
	s.mu.Unlock()
	var errs []error
	if h3server != nil {
		if err := h3server.Close(); err != nil && !benignServerError(err) {
			errs = append(errs, err)
		}
	}
	if nativeServer != nil {
		if err := nativeServer.Close(); err != nil && !benignServerError(err) {
			errs = append(errs, err)
		}
	}
	if httpServer != nil {
		if err := httpServer.Close(); err != nil && !benignServerError(err) {
			errs = append(errs, err)
		}
	}
	if tcp != nil {
		if err := tcp.Close(); err != nil && !benignServerError(err) {
			errs = append(errs, err)
		}
	}
	if udp != nil {
		if err := udp.Close(); err != nil && !benignServerError(err) {
			errs = append(errs, err)
		}
	}
	return errors.Join(errs...)
}
