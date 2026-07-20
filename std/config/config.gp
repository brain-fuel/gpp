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
