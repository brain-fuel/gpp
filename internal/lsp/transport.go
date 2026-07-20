// Package lsp is goplus's language server. The transport and the heavy
// lifting (generation, gopls delegation) are plain Go; the request
// dispatch is authored in goplus (handlers.gp) — the server is
// extensible in the language it serves, and it ships inside the goplus
// binary, so its version IS the language version.
package lsp

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io"
	"strconv"
	"strings"
)

// message is a JSON-RPC 2.0 envelope (request, response, or
// notification — distinguished by which fields are set).
type message struct {
	JSONRPC string           `json:"jsonrpc"`
	ID      *json.RawMessage `json:"id,omitempty"`
	Method  string           `json:"method,omitempty"`
	Params  json.RawMessage  `json:"params,omitempty"`
	Result  any              `json:"result,omitempty"`
	Error   *respError       `json:"error,omitempty"`
}

type respError struct {
	Code    int    `json:"code"`
	Message string `json:"message"`
}

// conn frames messages with Content-Length headers.
type conn struct {
	r *bufio.Reader
	w io.Writer
}

func newConn(r io.Reader, w io.Writer) *conn {
	return &conn{r: bufio.NewReader(r), w: w}
}

func (c *conn) read() (*message, error) {
	length := -1
	for {
		line, err := c.r.ReadString('\n')
		if err != nil {
			return nil, err
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			break
		}
		if v, ok := strings.CutPrefix(line, "Content-Length: "); ok {
			n, cerr := strconv.Atoi(strings.TrimSpace(v))
			if cerr != nil {
				return nil, fmt.Errorf("bad Content-Length %q", v)
			}
			length = n
		}
	}
	if length < 0 {
		return nil, fmt.Errorf("missing Content-Length")
	}
	buf := make([]byte, length)
	if _, err := io.ReadFull(c.r, buf); err != nil {
		return nil, err
	}
	var m message
	if err := json.Unmarshal(buf, &m); err != nil {
		return nil, err
	}
	return &m, nil
}

func (c *conn) write(m *message) error {
	m.JSONRPC = "2.0"
	buf, err := json.Marshal(m)
	if err != nil {
		return err
	}
	if _, err := fmt.Fprintf(c.w, "Content-Length: %d\r\n\r\n", len(buf)); err != nil {
		return err
	}
	_, err = c.w.Write(buf)
	return err
}

// respond sends a result for a request id.
func (c *conn) respond(id *json.RawMessage, result any) error {
	return c.write(&message{ID: id, Result: result})
}

// respondErr sends an error for a request id.
func (c *conn) respondErr(id *json.RawMessage, code int, msg string) error {
	return c.write(&message{ID: id, Error: &respError{Code: code, Message: msg}})
}

// notify sends a server-initiated notification.
func (c *conn) notify(method string, params any) error {
	raw, err := json.Marshal(params)
	if err != nil {
		return err
	}
	return c.write(&message{Method: method, Params: raw})
}
