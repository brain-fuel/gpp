// Package route provides immutable, pattern-indexed HTTP route values. Pattern
// identities are opt-in natural indices: Go+ checks them, generated Go retains
// IDs for erased-boundary guards, and ordinary net/http remains the wire API.
package route

import (
	"fmt"
	"net/http"
	"strings"
)

type SegmentKind enum {
	StaticKind()
	ParameterKind()
	WildcardKind()
}

type Segment struct { Kind SegmentKind; Text string; Name string }

// Capability makes middleware effects explicit instead of hiding them in an
// arbitrary handler wrapper.
type Capability enum {
	ObserveRequest()
	WriteHeaders()
	ReadBody()
	MutateState()
}

total func ObserveRequestID() nat { return 1 }
total func WriteHeadersID() nat { return 2 }
total func ReadBodyID() nat { return 3 }
total func MutateStateID() nat { return 4 }

// Middleware[c] carries one declared capability c.
//goplus:derive off
type Middleware[c nat] enum {
	middlewareValue(ID int, Capability Capability, Wrap func(http.Handler) http.Handler) Middleware[c]
}

// Pattern[p] is a parsed route pattern with singleton identity p.
//goplus:derive off
type Pattern[p nat] enum {
	patternValue(ID int, Text string, Segments []Segment, Names []string) Pattern[p]
}

type ParseOutcome[p nat] enum {
	PatternParsed(Pattern Pattern[p])
	InvalidPattern(Message string)
}

// Request[p] carries exactly the parameter environment produced by Pattern[p].
//goplus:derive off
type Request[p nat] enum {
	requestValue(PatternID int, PatternText string, Writer http.ResponseWriter, Raw *http.Request, Params map[string]string) Request[p]
}

// Handler[p] is sealed handler code for Pattern[p].
//goplus:derive off
type Handler[p nat] enum {
	handlerValue(PatternID int, PatternText string, Run func(Request[p])) Handler[p]
}

// ParamKey[T,p] decodes one named parameter belonging to Pattern[p].
//goplus:derive off
type ParamKey[T any, p nat] enum {
	paramKeyValue(PatternID int, PatternText string, Name string, Decode func(string) (T, bool)) ParamKey[T, p]
}

type ParamResult[T any] enum {
	ParamMissing()
	ParamInvalid(Raw string)
	ParamFound(Value T)
}

type Metadata struct { Method string; Pattern string; PatternID int; ParamNames []string }

// Registered[p] ties handler metadata to Pattern[p].
//goplus:derive off
type Registered[p nat] enum {
	registeredValue(Metadata Metadata) Registered[p]
}

// RouteSet[s] is an immutable route-set fingerprint. Add changes s using a
// collision-free pairing function, so separately assembled sets cannot mix.
//goplus:derive off
type RouteSet[s nat] enum {
	routeSetValue(Fingerprint int, Routes []Metadata) RouteSet[s]
}

type AddOutcome[s nat] enum {
	RouteAdded(Set RouteSet[s])
	RouteConflict(Existing Metadata, Incoming Metadata)
}

total func RouteSetID(set nat, route nat) nat {
	return ((set+route)*(set+route+1)+route)+1
}

func parse(text string) ([]Segment, []string, error) {
	if text == "" || text[0] != '/' { return nil, nil, fmt.Errorf("route: pattern must begin with '/'") }
	if text == "/" { return nil, nil, nil }
	parts := strings.Split(strings.TrimPrefix(text, "/"), "/")
	segments := make([]Segment, 0, len(parts))
	names := make([]string, 0)
	seen := make(map[string]bool)
	for i, part := range parts {
		segment := Segment{Kind: StaticKind(), Text: part}
		if part == "*" {
			segment = Segment{Kind: WildcardKind(), Name: "*"}
		} else if strings.HasPrefix(part, "{") && strings.HasSuffix(part, "}") {
			body := part[1:len(part)-1]
			name, expression, hasExpression := strings.Cut(body, ":")
			if name == "" { return nil, nil, fmt.Errorf("route: empty parameter") }
			if hasExpression && expression != "*" && expression != ".*" { return nil, nil, fmt.Errorf("route: typed core does not accept regex parameters") }
			if hasExpression { segment = Segment{Kind: WildcardKind(), Name: name} } else { segment = Segment{Kind: ParameterKind(), Name: name} }
		}
		if !SegmentKindEqual(segment.Kind, StaticKind()) {
			if seen[segment.Name] { return nil, nil, fmt.Errorf("route: duplicate parameter %q", segment.Name) }
			if SegmentKindEqual(segment.Kind, WildcardKind()) && i != len(parts)-1 { return nil, nil, fmt.Errorf("route: wildcard must be final") }
			seen[segment.Name] = true
			names = append(names, segment.Name)
		}
		segments = append(segments, segment)
	}
	return segments, names, nil
}

func Parse(id nat, text string) ParseOutcome[id] {
	if id < 0 { return InvalidPattern("route: negative pattern ID") }
	segments, names, err := parse(text)
	if err != nil { return InvalidPattern(err.Error()) }
	return PatternParsed(patternValue(int(id), text, segments, names))
}

func MustPattern(id nat, text string) Pattern[id] {
	if id < 0 { panic("route: negative pattern ID") }
	segments, names, err := parse(text)
	if err != nil { panic(err) }
	return patternValue(int(id), text, segments, names)
}

func Text(0 p nat, pattern Pattern[p]) string {
	match pattern { case patternValue(_, text, _, _): return text }
}

func PatternID(0 p nat, pattern Pattern[p]) int {
	match pattern { case patternValue(id, _, _, _): return id }
}

func NewMiddleware(id nat, capability Capability, wrap func(http.Handler) http.Handler) Middleware[id] {
	if id < 0 { panic("route: negative capability ID") }
	if wrap == nil { panic("route: nil middleware") }
	expected := 0
	match capability {
	case ObserveRequest(): expected = int(ObserveRequestID())
	case WriteHeaders(): expected = int(WriteHeadersID())
	case ReadBody(): expected = int(ReadBodyID())
	case MutateState(): expected = int(MutateStateID())
	}
	if int(id) != expected { panic("route: capability ID does not match capability") }
	return middlewareValue(int(id), capability, wrap)
}

func Observer(wrap func(http.Handler) http.Handler) Middleware[ObserveRequestID()] { return NewMiddleware(ObserveRequestID(), ObserveRequest(), wrap) }
func HeaderWriter(wrap func(http.Handler) http.Handler) Middleware[WriteHeadersID()] { return NewMiddleware(WriteHeadersID(), WriteHeaders(), wrap) }
func BodyReader(wrap func(http.Handler) http.Handler) Middleware[ReadBodyID()] { return NewMiddleware(ReadBodyID(), ReadBody(), wrap) }
func StateMutator(wrap func(http.Handler) http.Handler) Middleware[MutateStateID()] { return NewMiddleware(MutateStateID(), MutateState(), wrap) }

func Wrap(0 c nat, middleware Middleware[c]) func(http.Handler) http.Handler {
	match middleware { case middlewareValue(_, _, wrap): return wrap }
}

func CapabilityOf(0 c nat, middleware Middleware[c]) Capability {
	match middleware { case middlewareValue(_, capability, _): return capability }
}

func NewHandler(0 p nat, pattern Pattern[p], run func(Request[p])) Handler[p] {
	if run == nil { panic("route: nil handler") }
	match pattern { case patternValue(id, text, _, _): return handlerValue(id, text, run) }
}

func NewParamKey[T any](0 p nat, pattern Pattern[p], name string, decode func(string) (T, bool)) ParamKey[T, p] {
	if name == "" { panic("route: empty parameter name") }
	if decode == nil { panic("route: nil parameter decoder") }
	match pattern {
	case patternValue(patternID, text, _, names):
		found := false
		for _, declared := range names { if declared == name { found = true } }
		if !found { panic("route: parameter is not declared by pattern") }
		return paramKeyValue(patternID, text, name, decode)
	}
}

func Param[T any](0 p nat, request Request[p], key ParamKey[T, p]) ParamResult[T] {
	match request {
	case requestValue(patternID, patternText, _, _, params):
		match key {
		case paramKeyValue(keyPatternID, keyPatternText, name, decode):
			if patternID != keyPatternID || patternText != keyPatternText { panic("route: parameter key belongs to another pattern") }
			raw, ok := params[name]
			if !ok { return ParamMissing[T]() }
			value, ok := decode(raw)
			if !ok { return ParamInvalid[T](raw) }
			return ParamFound(value)
		}
	}
}

func Raw(0 p nat, request Request[p]) *http.Request {
	match request { case requestValue(_, _, _, raw, _): return raw }
}

func Writer(0 p nat, request Request[p]) http.ResponseWriter {
	match request { case requestValue(_, _, writer, _, _): return writer }
}

func patternMatch(segments []Segment, path string) (map[string]string, bool) {
	parts := []string{}
	if path != "/" && path != "" { parts = strings.Split(strings.TrimPrefix(path, "/"), "/") }
	params := make(map[string]string)
	part := 0
	for _, segment := range segments {
		if SegmentKindEqual(segment.Kind, WildcardKind()) {
			params[segment.Name] = strings.Join(parts[part:], "/")
			part = len(parts)
			break
		}
		if part >= len(parts) { return nil, false }
		if SegmentKindEqual(segment.Kind, StaticKind()) {
			if parts[part] != segment.Text { return nil, false }
		} else {
			params[segment.Name] = parts[part]
		}
		part++
	}
	return params, part == len(parts)
}

// Adapt turns a pattern-indexed handler into ordinary net/http. It validates
// the path independently, making std/http/route useful without any router.
func Adapt(0 p nat, pattern Pattern[p], handler Handler[p]) http.Handler {
	match pattern {
	case patternValue(patternID, patternText, segments, _):
		match handler {
		case handlerValue(handlerPatternID, handlerPatternText, run):
			if patternID != handlerPatternID || patternText != handlerPatternText { panic("route: handler belongs to another pattern") }
			return http.HandlerFunc(func(writer http.ResponseWriter, raw *http.Request) {
				params, ok := patternMatch(segments, raw.URL.Path)
				if !ok { panic("route: handler invoked for a non-matching path") }
				run(requestValue(patternID, patternText, writer, raw, params))
			})
		}
	}
}

func Register(method string, 0 p nat, pattern Pattern[p]) Registered[p] {
	if method == "" { panic("route: empty method") }
	match pattern {
	case patternValue(id, text, _, names):
		return registeredValue(Metadata{Method: strings.ToUpper(method), Pattern: text, PatternID: id, ParamNames: append([]string(nil), names...)})
	}
}

func Empty() RouteSet[0] { return routeSetValue(0, nil) }

func routeSetFingerprint(set int, route int) int { return (set+route)*(set+route+1)+route+1 }

func Add(0 s nat, routeID nat, set RouteSet[s], route Registered[routeID]) AddOutcome[RouteSetID(s, routeID)] {
	match set {
	case routeSetValue(fingerprint, routes):
		match route {
		case registeredValue(incoming):
			for _, existing := range routes {
				if existing.Method == incoming.Method && existing.Pattern == incoming.Pattern { return RouteConflict(existing, incoming) }
			}
			owned := append([]Metadata(nil), routes...)
			owned = append(owned, incoming)
			return RouteAdded(routeSetValue(routeSetFingerprint(fingerprint, int(routeID)), owned))
		}
	}
}

func Routes(0 s nat, set RouteSet[s]) []Metadata {
	match set {
	case routeSetValue(_, routes):
		owned := append([]Metadata(nil), routes...)
		for i := range owned { owned[i].ParamNames = append([]string(nil), owned[i].ParamNames...) }
		return owned
	}
}
