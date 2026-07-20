package lsp

import (
	"encoding/json"
	"fmt"
	"os/exec"
	"sync"
)

// goplsClient manages a gopls subprocess speaking LSP over the
// GENERATED Go files: goplus positions forward through the sourcemap,
// gopls answers over plain Go, results map back. One request in
// flight at a time — editor traffic, not throughput.
type goplsClient struct {
	cmd  *exec.Cmd
	conn *conn
	mu   sync.Mutex
	next int
	open map[string]int // generated path → version
}

// startGopls launches the delegate; nil (graceful degradation) when
// gopls is not installed or fails to start.
func startGopls(root string) *goplsClient {
	path, err := exec.LookPath("gopls")
	if err != nil {
		return nil
	}
	cmd := exec.Command(path, "serve")
	cmd.Dir = root
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return nil
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil
	}
	if err := cmd.Start(); err != nil {
		return nil
	}
	c := &goplsClient{cmd: cmd, conn: newConn(stdout, stdin), next: 1, open: map[string]int{}}
	if _, err := c.request("initialize", map[string]any{
		"rootUri":      pathToURI(root),
		"capabilities": map[string]any{},
	}); err != nil {
		c.stop()
		return nil
	}
	_ = c.conn.notify("initialized", map[string]any{})
	return c
}

func (c *goplsClient) stop() {
	if c.cmd != nil && c.cmd.Process != nil {
		_ = c.cmd.Process.Kill()
	}
}

// request sends one request and reads until its response arrives
// (server-to-client notifications in between are drained).
func (c *goplsClient) request(method string, params any) (json.RawMessage, error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	id := c.next
	c.next++
	raw, err := json.Marshal(params)
	if err != nil {
		return nil, err
	}
	idRaw := json.RawMessage(fmt.Sprintf("%d", id))
	if err := c.conn.write(&message{ID: &idRaw, Method: method, Params: raw}); err != nil {
		return nil, err
	}
	for {
		m, err := c.conn.read()
		if err != nil {
			return nil, err
		}
		if m.ID == nil || string(*m.ID) != string(idRaw) {
			continue // notification or unrelated traffic
		}
		if m.Error != nil {
			return nil, fmt.Errorf("gopls: %s", m.Error.Message)
		}
		out, merr := json.Marshal(m.Result)
		return out, merr
	}
}

// syncOutputs pushes the latest generated texts as open documents.
func (c *goplsClient) syncOutputs(outputs map[string][]byte) {
	c.mu.Lock()
	defer c.mu.Unlock()
	for path, content := range outputs {
		uri := pathToURI(path)
		if v, isOpen := c.open[path]; isOpen {
			c.open[path] = v + 1
			_ = c.conn.notify("textDocument/didChange", map[string]any{
				"textDocument":   map[string]any{"uri": uri, "version": v + 1},
				"contentChanges": []map[string]any{{"text": string(content)}},
			})
			continue
		}
		c.open[path] = 1
		_ = c.conn.notify("textDocument/didOpen", map[string]any{
			"textDocument": map[string]any{
				"uri": uri, "languageId": "go", "version": 1, "text": string(content),
			},
		})
	}
}
