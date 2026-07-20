// Package cbor provides RFC 8949 CBOR serialization for Go and Go+.
//
// Marshal uses deterministic RFC 8949 encoding by default. Unmarshal accepts
// all well-formed RFC 8949 / RFC 7049 encodings but rejects duplicate map keys
// and unreasonable nesting or collection sizes. Legacy is available when an
// application explicitly needs RFC 7049 canonical map ordering.
package cbor

import (
	"io"

	fcbor "github.com/fxamacker/cbor/v2"
)

// MediaType is the IANA media type registered by RFC 8949.
const MediaType = "application/cbor"

var (
	defaultEnc = mustEnc(fcbor.CoreDetEncOptions())
	legacyEnc  = mustEnc(fcbor.CanonicalEncOptions())
	defaultDec = mustDec(fcbor.DecOptions{
		DupMapKey:        fcbor.DupMapKeyEnforcedAPF,
		MaxNestedLevels:  64,
		MaxArrayElements: 1 << 20,
		MaxMapPairs:      1 << 20,
		UTF8:             fcbor.UTF8RejectInvalid,
	})
)

// Standard CBOR extension points and data-model values are aliases, so custom
// implementations interoperate directly with the underlying RFC codec.
type (
	Marshaler   = fcbor.Marshaler
	Unmarshaler = fcbor.Unmarshaler
	RawMessage  = fcbor.RawMessage
	Tag         = fcbor.Tag
	RawTag      = fcbor.RawTag
	SimpleValue = fcbor.SimpleValue
	Encoder     = fcbor.Encoder
	Decoder     = fcbor.Decoder
)

func mustEnc(options fcbor.EncOptions) fcbor.EncMode {
	mode, err := options.EncMode()
	if err != nil {
		panic(err)
	}
	return mode
}

func mustDec(options fcbor.DecOptions) fcbor.DecMode {
	mode, err := options.DecMode()
	if err != nil {
		panic(err)
	}
	return mode
}

// Marshal encodes value using RFC 8949 core deterministic encoding. This is a
// stable default for signatures, hashes, caches, and ordinary interchange.
func Marshal(value any) ([]byte, error) { return defaultEnc.Marshal(value) }

// Unmarshal decodes exactly one CBOR data item into dst. Trailing data and
// duplicate map keys are rejected.
func Unmarshal(data []byte, dst any) error { return defaultDec.Unmarshal(data, dst) }

// UnmarshalFirst decodes the first item in a CBOR sequence and returns the
// untouched remainder. Use Unmarshal when exactly one item is required.
func UnmarshalFirst(data []byte, dst any) ([]byte, error) {
	return defaultDec.UnmarshalFirst(data, dst)
}

// NewEncoder returns a streaming encoder with deterministic RFC 8949 output.
func NewEncoder(w io.Writer) *Encoder { return defaultEnc.NewEncoder(w) }

// NewDecoder returns a streaming decoder with the same safety limits as
// Unmarshal. Consecutive Decode calls consume a CBOR sequence.
func NewDecoder(r io.Reader) *Decoder { return defaultDec.NewDecoder(r) }

// Diagnose renders RFC 8949 diagnostic notation for exactly one item.
func Diagnose(data []byte) (string, error) { return fcbor.Diagnose(data) }

// Valid reports whether data contains exactly one well-formed CBOR data item.
func Valid(data []byte) error {
	var value any
	return defaultDec.Unmarshal(data, &value)
}

// Codec is a typed serde codec using the safe defaults of Marshal and
// Unmarshal. Its zero value is ready for use.
type Codec[T any] struct{}

func (Codec[T]) Marshal(value T) ([]byte, error) { return Marshal(value) }
func (Codec[T]) Unmarshal(data []byte) (T, error) {
	var value T
	err := Unmarshal(data, &value)
	return value, err
}
func (Codec[T]) MediaType() string { return MediaType }

// LegacyCodec uses RFC 7049 canonical encoding. RFC 8949 kept wire-format
// compatibility, so decoding uses the same safe decoder as Codec.
type LegacyCodec[T any] struct{}

func (LegacyCodec[T]) Marshal(value T) ([]byte, error)  { return legacyEnc.Marshal(value) }
func (LegacyCodec[T]) Unmarshal(data []byte) (T, error) { return Codec[T]{}.Unmarshal(data) }
func (LegacyCodec[T]) MediaType() string                { return MediaType }
