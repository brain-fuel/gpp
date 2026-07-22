// Package config layers defaults, decoding, and semantic validation while
// retaining field paths in diagnostics.
package config

import (
	"fmt"
	"strings"
)

// Decoder overlays serialized fields onto base. This lets format adapters
// preserve schema defaults without coupling this package to JSON, YAML, etc.
type Decoder[T any] interface { Decode([]byte, T) (T, error) }
type Validator[T any] interface { Validate(T) error }
type ValidateFunc[T any] func(T) error
func (f ValidateFunc[T]) Validate(v T) error { return f(v) }

type FieldError struct { Path string; Err error }
func (e *FieldError) Error() string {
	if e.Path == "" { return e.Err.Error() }
	return e.Path + ": " + e.Err.Error()
}
func (e *FieldError) Unwrap() error { return e.Err }
func At(path string, err error) error {
	if err == nil { return nil }
	return &FieldError{Path: path, Err: err}
}

type Schema[T any] struct {
	Defaults func() T
	Decoder Decoder[T]
	Validators []Validator[T]
}

func (s Schema[T]) Load(data []byte) (T, error) {
	var zero T
	if s.Decoder == nil { return zero, fmt.Errorf("config: nil decoder") }
	base := zero
	if s.Defaults != nil { base = s.Defaults() }
	v, err := s.Decoder.Decode(data, base)
	if err != nil { return zero, err }
	for _, validator := range s.Validators {
		if err := validator.Validate(v); err != nil { return zero, err }
	}
	return v, nil
}

type Errors []error
func (e Errors) Error() string {
	parts := make([]string, 0, len(e))
	for _, err := range e { if err != nil { parts = append(parts, err.Error()) } }
	return strings.Join(parts, "; ")
}
func Collect(errs ...error) error {
	out := Errors{}
	for _, err := range errs { if err != nil { out = append(out, err) } }
	if len(out) == 0 { return nil }
	return out
}

// Source identifies the winning layer for a resolved value. The declaration
// order is also the precedence order used by Resolve.
type Source enum {
	DefaultSource()
	RemoteSource()
	FileSource()
	EnvironmentSource()
	FlagSource()
	OverrideSource()
}

// Entry retains both the value and its provenance.
type Entry struct { Value any; Source Source }

// Layer is one immutable input to resolution. Resolve copies every map, so a
// Snapshot never aliases caller-owned mutable configuration.
type Layer struct { Source Source; Values map[string]any }

// Snapshot[s] is a resolved immutable configuration for schema s. The schema
// witness is retained for ordinary-Go boundary checks and erased from Go+
// call sites after dependent checking.
//goplus:derive off
type Snapshot[s nat] enum {
	snapshotValue(Schema int, Entries map[string]Entry) Snapshot[s]
}

// Key[T,s] is the only typed way to read T from Snapshot[s]. Independently
// constructed keys from another schema cannot be used with the snapshot.
//goplus:derive off
type Key[T any, s nat] enum {
	keyValue(Schema int, Name string, Decode func(any) (T, bool)) Key[T, s]
}

// Lookup distinguishes missing keys from values of the wrong runtime shape.
type Lookup[T any] enum {
	Missing()
	WrongType(Value any, Source Source)
	Found(Value T, Source Source)
}

// Present[T,s] is evidence that a particular typed key was present and
// decoded in schema s. It retains the key, value, and originating snapshot.
//goplus:derive off
type Present[T any, s nat] enum {
	presentValue(Snapshot Snapshot[s], Key Key[T, s], Value T, Source Source) Present[T, s]
}

// Requirement makes absence and malformed values explicit while producing a
// proof object on success.
type Requirement[T any, s nat] enum {
	Available(Present Present[T, s])
	RequiredMissing()
	RequiredWrongType(Value any, Source Source)
}

// Subset[s,sub] is evidence that a named projection from schema s to schema
// sub has been declared. Runtime schema IDs defend the erased Go boundary.
//goplus:derive off
type Subset[s nat, sub nat] enum {
	subsetValue(SourceSchema int, TargetSchema int, Names []string) Subset[s, sub]
}

func NewKey[T any](schema nat, name string, decode func(any) (T, bool)) Key[T, schema] {
	if schema < 0 { panic("config: negative schema ID") }
	if name == "" { panic("config: empty key") }
	if decode == nil { panic("config: nil key decoder") }
	return keyValue(int(schema), strings.ToLower(name), decode)
}

// Resolve deterministically applies layers from lowest to highest precedence.
// Repeated source kinds retain caller order within that precedence level.
func Resolve(schema nat, layers ...Layer) Snapshot[schema] {
	if schema < 0 { panic("config: negative schema ID") }
	entries := make(map[string]Entry)
	sources := []Source{DefaultSource(), RemoteSource(), FileSource(), EnvironmentSource(), FlagSource(), OverrideSource()}
	for _, source := range sources {
		for _, layer := range layers {
			if !SourceEqual(layer.Source, source) { continue }
			for name, value := range layer.Values {
				entries[strings.ToLower(name)] = Entry{Value: cloneConfigValue(value), Source: source}
			}
		}
	}
	return snapshotValue(int(schema), entries)
}

func Get[T any](0 s nat, snapshot Snapshot[s], key Key[T, s]) Lookup[T] {
	match snapshot {
	case snapshotValue(schema, entries):
		match key {
		case keyValue(keySchema, name, decode):
			if schema != keySchema { panic("config: key belongs to a different schema") }
			entry, ok := entries[name]
			if !ok { return Missing[T]() }
			owned := cloneConfigValue(entry.Value)
			value, ok := decode(owned)
			if !ok { return WrongType[T](owned, entry.Source) }
			return Found(value, entry.Source)
		}
	}
}

func Untyped(0 s nat, snapshot Snapshot[s], name string) (Entry, bool) {
	match snapshot {
	case snapshotValue(_, entries):
		entry, ok := entries[strings.ToLower(name)]
		entry.Value = cloneConfigValue(entry.Value)
		return entry, ok
	}
}

func cloneConfigValue(value any) any {
	switch x := value.(type) {
	case map[string]any:
		out := make(map[string]any, len(x))
		for key, item := range x { out[key] = cloneConfigValue(item) }
		return out
	case []any:
		out := make([]any, len(x))
		for i, item := range x { out[i] = cloneConfigValue(item) }
		return out
	case []string: return append([]string(nil), x...)
	case []int: return append([]int(nil), x...)
	default: return value
	}
}

func Require[T any](0 s nat, snapshot Snapshot[s], key Key[T, s]) Requirement[T, s] {
	match Get(snapshot, key) {
	case Missing(): return RequiredMissing[T]()
	case WrongType(value, source): return RequiredWrongType[T](value, source)
	case Found(value, source): return Available(presentValue(snapshot, key, value, source))
	}
}

func RequiredValue[T any](0 s nat, proof Present[T, s]) T {
	match proof { case presentValue(_, _, value, _): return value }
}

func NewSubset(sourceSchema nat, targetSchema nat, names ...string) Subset[sourceSchema, targetSchema] {
	if sourceSchema < 0 || targetSchema < 0 { panic("config: negative schema ID") }
	owned := make([]string, len(names))
	for i, name := range names {
		if name == "" { panic("config: empty subset key") }
		owned[i] = strings.ToLower(name)
	}
	return subsetValue(int(sourceSchema), int(targetSchema), owned)
}

func Project(0 s nat, 0 sub nat, snapshot Snapshot[s], subset Subset[s, sub]) Snapshot[sub] {
	match snapshot {
	case snapshotValue(schema, entries):
		match subset {
		case subsetValue(sourceSchema, targetSchema, names):
			if schema != sourceSchema { panic("config: subset belongs to a different source schema") }
			projected := make(map[string]Entry)
			for _, name := range names {
				if entry, ok := entries[name]; ok { projected[name] = entry }
			}
			return snapshotValue(targetSchema, projected)
		}
	}
}
