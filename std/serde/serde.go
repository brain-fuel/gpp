// Package serde defines the small common surface shared by Go+ standard
// library serializers.  Codecs are ordinary Go values and work unchanged
// from Go and Go+.
package serde

// Codec serializes values of T to one wire format.
type Codec[T any] interface {
	Marshal(T) ([]byte, error)
	Unmarshal([]byte) (T, error)
	MediaType() string
}

// Marshal serializes value with codec.  It is useful when the codec is passed
// as an interface rather than used directly.
func Marshal[T any](codec Codec[T], value T) ([]byte, error) {
	return codec.Marshal(value)
}

// Unmarshal deserializes one complete value with codec.
func Unmarshal[T any](codec Codec[T], data []byte) (T, error) {
	return codec.Unmarshal(data)
}
