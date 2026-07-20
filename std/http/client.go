package http

import (
	"io"
	nethttp "net/http"
	"net/url"
)

// DefaultTransport automatically learns HTTP/3 through Alt-Svc and safely
// falls back through HTTP/2 and HTTP/1.1. It is shared by DefaultClient.
var DefaultTransport = &Transport{}

// DefaultClient is ready for ordinary HTTP use with automatic HTTP/3. Its
// methods have the same shape as net/http.Client.
var DefaultClient = &nethttp.Client{Transport: DefaultTransport}

// Get uses DefaultClient, including automatic HTTP/3 discovery and fallback.
func Get(url string) (*nethttp.Response, error) { return DefaultClient.Get(url) }

// Head uses DefaultClient, including automatic HTTP/3 discovery and fallback.
func Head(url string) (*nethttp.Response, error) { return DefaultClient.Head(url) }

// Post uses DefaultClient, including automatic HTTP/3 discovery and fallback.
func Post(url, contentType string, body io.Reader) (*nethttp.Response, error) {
	return DefaultClient.Post(url, contentType, body)
}

// PostForm uses DefaultClient, including automatic HTTP/3 discovery and
// fallback.
func PostForm(target string, data url.Values) (*nethttp.Response, error) {
	return DefaultClient.PostForm(target, data)
}
