package route

import (
	"io"
	"net/http"
	"net/http/httptest"
	"strconv"
	"testing"
)

func TestPatternIndexedAdapterAndTypedParameter(t *testing.T) {
	pattern := MustPattern(7, "/users/{id}")
	id := NewParamKey(pattern, "id", func(raw string) (int, bool) { value, err := strconv.Atoi(raw); return value, err == nil })
	typed := NewHandler(pattern, func(request Request) {
		result := Param(request, id)
		found, ok := result.(ParamFound[int])
		if !ok || found.Value != 42 {
			t.Errorf("Param = %#v", result)
		}
		_, _ = io.WriteString(Writer(request), "ok")
	})
	handler := Adapt(pattern, typed)
	recorder := httptest.NewRecorder()
	request := httptest.NewRequest("GET", "/users/42", nil)
	handler.ServeHTTP(recorder, request)
	if recorder.Body.String() != "ok" {
		t.Fatalf("body = %q", recorder.Body.String())
	}
}

func TestCapabilityIndexedMiddleware(t *testing.T) {
	middleware := NewMiddleware(WriteHeadersID(), WriteHeaders{}, func(next http.Handler) http.Handler {
		return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) { w.Header().Set("X-Typed", "yes"); next.ServeHTTP(w, r) })
	})
	handler := Wrap(middleware)(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) { w.WriteHeader(http.StatusNoContent) }))
	recorder := httptest.NewRecorder()
	handler.ServeHTTP(recorder, httptest.NewRequest("GET", "/", nil))
	if recorder.Code != http.StatusNoContent || recorder.Header().Get("X-Typed") != "yes" {
		t.Fatalf("response = %d %v", recorder.Code, recorder.Header())
	}
	if !CapabilityEqual(CapabilityOf(middleware), WriteHeaders{}) {
		t.Fatal("capability witness changed")
	}
}

func TestParseOutcomeIsExplicit(t *testing.T) {
	if _, ok := Parse(1, "/users/{id}").(PatternParsed); !ok {
		t.Fatal("valid pattern rejected")
	}
	if _, ok := Parse(1, "users/{id}").(InvalidPattern); !ok {
		t.Fatal("invalid pattern accepted")
	}
}

func FuzzTypedPatternParser(f *testing.F) {
	for _, pattern := range []string{"/", "/health", "/users/{id}", "/files/*", "bad"} {
		f.Add(pattern)
	}
	f.Fuzz(func(t *testing.T, pattern string) { _ = Parse(9, pattern) })
}

func TestPlainGoPatternGuard(t *testing.T) {
	pattern := MustPattern(7, "/users/{id}")
	foreignPattern := MustPattern(8, "/users/{id}")
	foreign := NewParamKey(foreignPattern, "id", func(raw string) (string, bool) { return raw, true })
	typed := NewHandler(pattern, func(request Request) {
		defer func() {
			if recover() == nil {
				t.Error("foreign key did not panic")
			}
		}()
		_ = Param(request, foreign)
	})
	handler := Adapt(pattern, typed)
	handler.ServeHTTP(httptest.NewRecorder(), httptest.NewRequest("GET", "/users/42", nil))
}

func TestPlainGoGuardRejectsReusedIDWithDifferentPatternText(t *testing.T) {
	users := MustPattern(7, "/users/{id}")
	teams := MustPattern(7, "/teams/{id}")
	foreign := NewParamKey(teams, "id", func(raw string) (string, bool) { return raw, true })
	typed := NewHandler(users, func(request Request) {
		defer func() {
			if recover() == nil {
				t.Error("same-ID foreign key did not panic")
			}
		}()
		_ = Param(request, foreign)
	})
	Adapt(users, typed).ServeHTTP(httptest.NewRecorder(), httptest.NewRequest("GET", "/users/42", nil))
}

func TestRouteSetConflictAndOwnership(t *testing.T) {
	pattern := MustPattern(3, "/health")
	registered := Register("GET", pattern)
	first := Add(3, Empty(), registered)
	added, ok := first.(RouteAdded)
	if !ok {
		t.Fatalf("first Add = %#v", first)
	}
	second := Add(3, added.Set, registered)
	if _, ok := second.(RouteConflict); !ok {
		t.Fatalf("duplicate Add = %#v", second)
	}
	routes := Routes(added.Set)
	routes[0].Pattern = "mutated"
	if Routes(added.Set)[0].Pattern != "/health" {
		t.Fatal("Routes exposed set storage")
	}
}
