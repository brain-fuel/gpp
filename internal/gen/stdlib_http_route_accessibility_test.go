package gen

import (
	"bytes"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func routeConsumerModule(t *testing.T, source string) string {
	t.Helper()
	dir := t.TempDir()
	std, err := filepath.Abs("../../std")
	if err != nil {
		t.Fatal(err)
	}
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/routeaccess\n\ngo 1.25.0\n\nrequire goforge.dev/goplus/std v0.0.0\nreplace goforge.dev/goplus/std => "+std+"\n")
	writeRefinementTestFile(t, dir, "main.gp", source)
	return dir
}

func TestGoPlusConsumesPatternIndexedHTTPRoute(t *testing.T) {
	dir := routeConsumerModule(t, `package main

import (
	"fmt"
	"net/http/httptest"
	"goforge.dev/goplus/std/http/route"
)

func main() {
	pattern := route.MustPattern(7, "/users/{id}")
	id := route.NewParamKey[int](7, pattern, "id", func(raw string) (int, bool) { return len(raw), true })
	typed := route.NewHandler(7, pattern, func(request route.Request[7]) {
		match route.Param(7, request, id) {
		case route.ParamFound(value): fmt.Fprint(route.Writer(7, request), value)
		case route.ParamMissing(): fmt.Fprint(route.Writer(7, request), "missing")
		case route.ParamInvalid(_): fmt.Fprint(route.Writer(7, request), "invalid")
		}
	})
	handler := route.Adapt(7, pattern, typed)
	recorder := httptest.NewRecorder()
	handler.ServeHTTP(recorder, httptest.NewRequest("GET", "/users/alice", nil))
	fmt.Println(recorder.Body.String())
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if !res.Ok() {
		t.Fatalf("generation diagnostics: %+v", res.Diags)
	}
	cmd := exec.Command("go", "run", "-mod=mod", ".")
	cmd.Dir = dir
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("Go+ route consumer: %v\n%s", err, stderr.Bytes())
	}
	if got := stdout.String(); got != "5\n" {
		t.Fatalf("output = %q", got)
	}
}

func assertRouteRejected(t *testing.T, source string) {
	t.Helper()
	dir := routeConsumerModule(t, source)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal("mismatched route program unexpectedly type checked")
	}
	found := false
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "dependent index mismatch") {
			found = true
		}
	}
	if !found {
		t.Fatalf("diagnostics do not explain route mismatch: %+v", res.Diags)
	}
}

func TestPatternIndexedRouteRejectsForeignParameterEnvironment(t *testing.T) {
	assertRouteRejected(t, `package main
import "goforge.dev/goplus/std/http/route"
func main() {
	pattern := route.MustPattern(7, "/users/{id}")
	foreignPattern := route.MustPattern(8, "/teams/{id}")
	foreign := route.NewParamKey[string](8, foreignPattern, "id", func(raw string) (string, bool) { return raw, true })
	handler := route.NewHandler(7, pattern, func(request route.Request[7]) { _ = route.Param(7, request, foreign) })
	_ = route.Adapt(7, pattern, handler)
}`)
}

func TestPatternIndexedRouteRejectsHandlerForAnotherPattern(t *testing.T) {
	assertRouteRejected(t, `package main
import "goforge.dev/goplus/std/http/route"
func main() {
	pattern := route.MustPattern(7, "/users/{id}")
	foreignPattern := route.MustPattern(8, "/teams/{id}")
	handler := route.NewHandler(8, foreignPattern, func(request route.Request[8]) {})
	_ = route.Adapt(7, pattern, handler)
}`)
}

func TestRouteSetRejectsRegistrationWithWrongIdentity(t *testing.T) {
	assertRouteRejected(t, `package main
import "goforge.dev/goplus/std/http/route"
func main() {
	pattern := route.MustPattern(4, "/health")
	registered := route.Register("GET", 4, pattern)
	_ = route.Add(0, 3, route.Empty(), registered)
}`)
}

func TestCapabilityIndexedMiddlewareRejectsWrongEffect(t *testing.T) {
	assertRouteRejected(t, `package main
import (
	"net/http"
	"goforge.dev/goplus/std/http/route"
)
func requireHeaders(middleware route.Middleware[route.WriteHeadersID()]) {}
func main() {
	body := route.BodyReader(func(next http.Handler) http.Handler { return next })
	requireHeaders(body)
}`)
}
