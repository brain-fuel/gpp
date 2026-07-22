package http

import (
	"io"
	nethttp "net/http"
	"net/http/httptest"
	"testing"

	"goforge.dev/goplus/std/http/route"
)

func TestRouteHandlerBridgesTypedRouteIntoHTTPServerSurface(t *testing.T) {
	pattern := route.MustPattern(23, "/status/{name}")
	name := route.NewParamKey(pattern, "name", func(raw string) (string, bool) { return raw, true })
	handler := route.NewHandler(pattern, func(request route.Request) {
		value := route.Param(request, name).(route.ParamFound[string]).Value
		_, _ = io.WriteString(route.Writer(request), value)
	})
	server := httptest.NewServer(RouteHandler(pattern, handler))
	defer server.Close()
	response, err := nethttp.Get(server.URL + "/status/ready")
	if err != nil {
		t.Fatal(err)
	}
	defer response.Body.Close()
	body, err := io.ReadAll(response.Body)
	if err != nil || string(body) != "ready" {
		t.Fatalf("body = %q, %v", body, err)
	}
}
