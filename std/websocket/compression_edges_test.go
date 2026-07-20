package websocket

import (
	"bytes"
	"errors"
	"io"
	"sync"
	"testing"
)

type failingResetter struct{ error }

func (f failingResetter) Reset(io.Reader, []byte) error { return f.error }

func TestCompressionParserEdges(t *testing.T) {
	if err := (CompressionOptions{ClientMaxWindowBits: 7}).validate(); !errors.Is(err, ErrInvalidExtension) {
		t.Fatalf("window validation: %v", err)
	}
	if parts, err := splitHeaderList(`one; p="a,b", two`); err != nil || len(parts) != 2 {
		t.Fatalf("quoted list: %#v %v", parts, err)
	}
	for _, malformed := range []string{`one; p="unterminated`, `one; p="escape\`} {
		if _, err := splitHeaderList(malformed); !errors.Is(err, ErrInvalidExtension) {
			t.Fatalf("splitHeaderList(%q): %v", malformed, err)
		}
	}
	if exts, err := parseExtensions(" "); err != nil || exts != nil {
		t.Fatalf("empty extensions: %#v %v", exts, err)
	}
	for _, malformed := range []string{
		`one; p="unterminated`,
		`; p=x`,
		`one;`,
		`one; =x`,
		`one; p="unterminated`,
	} {
		if _, err := parseExtensions(malformed); !errors.Is(err, ErrInvalidExtension) {
			t.Fatalf("parseExtensions(%q): %v", malformed, err)
		}
	}
	if exts, err := parseExtensions(`one; p="quoted"`); err != nil || exts[0].params["p"] != "quoted" {
		t.Fatalf("quoted parameter: %#v %v", exts, err)
	}
	if _, err := parseExtensions(`one; p="bad\q"`); !errors.Is(err, ErrInvalidExtension) {
		t.Fatalf("invalid quoted parameter: %v", err)
	}
	if fields, err := splitDelimited(`one; p="a\";b"; q=x`, ';'); err != nil || len(fields) != 3 {
		t.Fatalf("splitDelimited: %#v %v", fields, err)
	}
	if _, err := splitDelimited(`one; p="unterminated`, ';'); !errors.Is(err, ErrInvalidExtension) {
		t.Fatalf("unterminated delimiter: %v", err)
	}
	if bits, err := windowBits("", true); err != nil || bits != 0 {
		t.Fatalf("empty bits: %d %v", bits, err)
	}
	for _, raw := range []string{"x", "7", "16"} {
		if _, err := windowBits(raw, false); !errors.Is(err, ErrInvalidExtension) {
			t.Fatalf("windowBits(%q): %v", raw, err)
		}
	}
	if _, err := compressionOffer(CompressionOptions{ServerMaxWindowBits: 16}); !errors.Is(err, ErrInvalidExtension) {
		t.Fatalf("invalid offer: %v", err)
	}
}

func TestCompressionResponseEveryRejection(t *testing.T) {
	base := CompressionOptions{ClientMaxWindowBits: 12, ServerMaxWindowBits: 12}
	if enabled, _, err := acceptCompressionResponse("", base); err != nil || enabled {
		t.Fatalf("empty response: %v %v", enabled, err)
	}
	for _, test := range []struct {
		header string
		opts   CompressionOptions
	}{
		{`permessage-deflate; p="unterminated`, base},
		{"x-extension", base},
		{"permessage-deflate; unknown", base},
		{"permessage-deflate", base},
		{"permessage-deflate; client_no_context_takeover; server_no_context_takeover", CompressionOptions{ClientMaxWindowBits: 12, ServerMaxWindowBits: 12, AllowClientContextTakeover: true}},
		{"permessage-deflate; server_no_context_takeover=true; client_no_context_takeover", base},
		{"permessage-deflate; server_no_context_takeover; client_no_context_takeover; client_max_window_bits=12", CompressionOptions{ServerMaxWindowBits: 12}},
		{"permessage-deflate; server_no_context_takeover; client_no_context_takeover; client_max_window_bits=7", base},
		{"permessage-deflate; server_no_context_takeover; client_no_context_takeover; client_max_window_bits=13", base},
		{"permessage-deflate; server_no_context_takeover; client_no_context_takeover; server_max_window_bits=7", base},
		{"permessage-deflate; server_no_context_takeover; client_no_context_takeover; server_max_window_bits=12", CompressionOptions{ClientMaxWindowBits: 12}},
		{"permessage-deflate; server_no_context_takeover; client_no_context_takeover; server_max_window_bits=13", base},
	} {
		if _, _, err := acceptCompressionResponse(test.header, test.opts); !errors.Is(err, ErrInvalidExtension) {
			t.Fatalf("accepted %q with %#v: %v", test.header, test.opts, err)
		}
	}
}

func TestCompressionNegotiationFallbacksAndContexts(t *testing.T) {
	if _, _, err := negotiateCompression("", CompressionOptions{ClientMaxWindowBits: 16}); !errors.Is(err, ErrInvalidExtension) {
		t.Fatalf("invalid config: %v", err)
	}
	if _, _, err := negotiateCompression(`permessage-deflate; p="unterminated`, CompressionOptions{}); !errors.Is(err, ErrInvalidExtension) {
		t.Fatalf("invalid syntax: %v", err)
	}
	for _, offer := range []string{
		"x-extension",
		"permessage-deflate; unknown",
		"permessage-deflate; server_no_context_takeover=true",
		"permessage-deflate; server_max_window_bits=7",
		"permessage-deflate; client_max_window_bits=7",
	} {
		if response, _, err := negotiateCompression(offer, CompressionOptions{}); err != nil || response != "" {
			t.Fatalf("offer %q: response=%q err=%v", offer, response, err)
		}
	}
	response, settings, err := negotiateCompression(
		"permessage-deflate; server_max_window_bits=14; client_max_window_bits",
		CompressionOptions{AllowServerContextTakeover: true, AllowClientContextTakeover: true},
	)
	if err != nil || response != "permessage-deflate; server_max_window_bits=14; client_max_window_bits=15" || settings.writeWindow != 14 || settings.readWindow != 15 || !settings.readContext {
		t.Fatalf("context negotiation: %q %#v %v", response, settings, err)
	}
	response, settings, err = negotiateCompression(
		"permessage-deflate; client_max_window_bits=9",
		CompressionOptions{ClientMaxWindowBits: 12},
	)
	if err != nil || response == "" || settings.readWindow != 9 {
		t.Fatalf("client limit: %q %#v %v", response, settings, err)
	}
}

func TestCompressionInflaterEdgesAndConcurrency(t *testing.T) {
	if decoder, err := acquireDeflater(0); err != nil {
		t.Fatal(err)
	} else {
		deflaterPools[15].Put(decoder)
	}
	if _, err := acquireDeflater(1); err == nil {
		t.Fatal("invalid deflater window accepted")
	}
	if _, err := deflateMessage(nil, 1); err == nil {
		t.Fatal("invalid deflate window accepted")
	}
	wantReset := errors.New("reset failed")
	if _, err := finishDeflate(nil, wantReset); !errors.Is(err, wantReset) {
		t.Fatalf("deflate write error: %v", err)
	}
	if _, err := finishDeflate([]byte{1, 2, 3, 4}, nil); !errors.Is(err, ErrInvalidExtension) {
		t.Fatalf("deflate trailer error: %v", err)
	}
	inflaterPool = sync.Pool{New: func() any {
		return &inflaterDecoder{reader: io.NopCloser(bytes.NewReader(nil)), reset: failingResetter{wantReset}}
	}}
	if _, err := acquireInflater(bytes.NewReader(nil), nil); !errors.Is(err, wantReset) {
		t.Fatalf("reset error: %v", err)
	}
	inflaterPool = sync.Pool{}
	failingAcquire := func(io.Reader, []byte) (*inflaterDecoder, error) { return nil, wantReset }
	if _, err := new(messageInflater).inflateWith(nil, 1, failingAcquire); !errors.Is(err, wantReset) {
		t.Fatalf("inflate acquire error: %v", err)
	}
	payload := bytes.Repeat([]byte("context-window"), 3000)
	compressed, err := deflateMessage(payload, 0)
	if err != nil {
		t.Fatal(err)
	}
	decoded, err := inflateMessage(compressed, 0)
	if err != nil || !bytes.Equal(decoded, payload) {
		t.Fatalf("unlimited inflate: %d %v", len(decoded), err)
	}
	contextual := &messageInflater{window: 8, context: true}
	if _, err := contextual.inflate(compressed, int64(len(payload))); err != nil {
		t.Fatal(err)
	}
	if len(contextual.history) != 1<<8 {
		t.Fatalf("history=%d", len(contextual.history))
	}
	if _, err := inflateMessage([]byte{0xff, 0xff, 0xff}, 100); err == nil {
		t.Fatal("corrupt deflate stream accepted")
	}
	errCh := make(chan error, 16)
	for range 16 {
		go func() {
			for range 100 {
				got, err := inflateMessage(compressed, int64(len(payload)))
				if err != nil || !bytes.Equal(got, payload) {
					errCh <- errors.New("concurrent inflate mismatch")
					return
				}
			}
			errCh <- nil
		}()
	}
	for range 16 {
		if err := <-errCh; err != nil {
			t.Fatal(err)
		}
	}
}
