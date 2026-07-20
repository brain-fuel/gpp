// Package dagcbor provides strict, deterministic DAG-CBOR serialization.
//
// Decode and Codec reject non-canonical encodings. Prove returns an immutable
// witness tying the decoded value to the exact canonical bytes and their
// SHA-256 digest, making the validation boundary explicit in Go and Go+ code.
package dagcbor

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"fmt"
	"math"

	fcbor "github.com/fxamacker/cbor/v2"
)

const MediaType = "application/vnd.ipld.dag-cbor"

var (
	encMode = mustEnc(fcbor.EncOptions{
		Sort:          fcbor.SortLengthFirst,
		ShortestFloat: fcbor.ShortestFloatNone,
		NaNConvert:    fcbor.NaNConvertNone,
		InfConvert:    fcbor.InfConvertNone,
		IndefLength:   fcbor.IndefLengthForbidden,
		TagsMd:        fcbor.TagsAllowed,
	})
	decMode = mustDec(fcbor.DecOptions{
		DupMapKey:        fcbor.DupMapKeyEnforcedAPF,
		MaxNestedLevels:  64,
		MaxArrayElements: 1 << 20,
		MaxMapPairs:      1 << 20,
		IndefLength:      fcbor.IndefLengthForbidden,
		TagsMd:           fcbor.TagsAllowed,
		UTF8:             fcbor.UTF8RejectInvalid,
	})
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

// Link is the binary CID carried by DAG-CBOR tag 42. It excludes the required
// 0x00 multibase identity prefix, which is added and checked on the wire.
type Link []byte

func (link Link) MarshalCBOR() ([]byte, error) {
	if len(link) == 0 {
		return nil, errors.New("dagcbor: empty CID")
	}
	payload := append([]byte{0}, link...)
	out := []byte{0xd8, 0x2a}
	out = appendHead(out, 2, uint64(len(payload)))
	out = append(out, payload...)
	return out, nil
}

func (link *Link) UnmarshalCBOR(data []byte) error {
	if link == nil {
		return errors.New("dagcbor: nil Link receiver")
	}
	var tag fcbor.Tag
	if err := decMode.Unmarshal(data, &tag); err != nil {
		return err
	}
	payload, ok := tag.Content.([]byte)
	if tag.Number != 42 || !ok || len(payload) < 2 || payload[0] != 0 {
		return errors.New("dagcbor: tag 42 must contain a 0x00-prefixed CID")
	}
	*link = append((*link)[:0], payload[1:]...)
	return nil
}

func appendHead(dst []byte, major byte, n uint64) []byte {
	prefix := major << 5
	switch {
	case n < 24:
		return append(dst, prefix|byte(n))
	case n <= math.MaxUint8:
		return append(dst, prefix|24, byte(n))
	case n <= math.MaxUint16:
		dst = append(dst, prefix|25)
		return binary.BigEndian.AppendUint16(dst, uint16(n))
	case n <= math.MaxUint32:
		dst = append(dst, prefix|26)
		return binary.BigEndian.AppendUint32(dst, uint32(n))
	default:
		dst = append(dst, prefix|27)
		return binary.BigEndian.AppendUint64(dst, n)
	}
}

// Marshal produces the unique DAG-CBOR representation of value or rejects a
// value outside the IPLD data model.
func Marshal(value any) ([]byte, error) {
	data, err := encMode.Marshal(value)
	if err != nil {
		return nil, err
	}
	if err := Validate(data); err != nil {
		return nil, err
	}
	return data, nil
}

// Unmarshal accepts only canonical DAG-CBOR containing one complete item.
func Unmarshal(data []byte, dst any) error {
	if err := Validate(data); err != nil {
		return err
	}
	return decMode.Unmarshal(data, dst)
}

// Validate proves that data is a single canonical DAG-CBOR item.
func Validate(data []byte) error {
	var value any
	if err := decMode.Unmarshal(data, &value); err != nil {
		return fmt.Errorf("dagcbor: invalid CBOR: %w", err)
	}
	if err := validateModel(value); err != nil {
		return err
	}
	canonical, err := encMode.Marshal(value)
	if err != nil {
		return fmt.Errorf("dagcbor: canonicalize: %w", err)
	}
	if !bytes.Equal(data, canonical) {
		return errors.New("dagcbor: encoding is not canonical")
	}
	return nil
}

func validateModel(value any) error {
	switch value := value.(type) {
	case nil, bool, string, []byte, uint64, int64:
		return nil
	case float64:
		if math.IsNaN(value) || math.IsInf(value, 0) {
			return errors.New("dagcbor: non-finite floats are outside the IPLD data model")
		}
		return nil
	case []any:
		for _, item := range value {
			if err := validateModel(item); err != nil {
				return err
			}
		}
		return nil
	case map[any]any:
		for key, item := range value {
			if _, ok := key.(string); !ok {
				return errors.New("dagcbor: map keys must be strings")
			}
			if err := validateModel(item); err != nil {
				return err
			}
		}
		return nil
	case fcbor.Tag:
		payload, ok := value.Content.([]byte)
		if value.Number != 42 || !ok || len(payload) < 2 || payload[0] != 0 {
			return errors.New("dagcbor: only tag 42 with a 0x00-prefixed CID is allowed")
		}
		return nil
	default:
		return fmt.Errorf("dagcbor: %T is outside the IPLD data model", value)
	}
}

// Proof witnesses that Bytes is canonical DAG-CBOR for Value. Proof values can
// only be constructed by Prove or MarshalProved.
type Proof[T any] struct {
	value  T
	bytes  []byte
	digest [sha256.Size]byte
}

func (proof Proof[T]) Value() T                  { return proof.value }
func (proof Proof[T]) Bytes() []byte             { return append([]byte(nil), proof.bytes...) }
func (proof Proof[T]) Digest() [sha256.Size]byte { return proof.digest }

// Prove validates canonical DAG-CBOR and decodes its value.
func Prove[T any](data []byte) (Proof[T], error) {
	var value T
	if err := Unmarshal(data, &value); err != nil {
		return Proof[T]{}, err
	}
	roundTrip, err := Marshal(value)
	if err != nil {
		return Proof[T]{}, err
	}
	if !bytes.Equal(data, roundTrip) {
		return Proof[T]{}, errors.New("dagcbor: canonical item does not round-trip through the requested Go type")
	}
	owned := append([]byte(nil), data...)
	return Proof[T]{value: value, bytes: owned, digest: sha256.Sum256(owned)}, nil
}

// MarshalProved encodes a value and returns its canonicality proof.
func MarshalProved[T any](value T) (Proof[T], error) {
	data, err := Marshal(value)
	if err != nil {
		return Proof[T]{}, err
	}
	return Proof[T]{value: value, bytes: data, digest: sha256.Sum256(data)}, nil
}

// Codec is a strict DAG-CBOR serde codec. Its zero value is ready for use.
type Codec[T any] struct{}

func (Codec[T]) Marshal(value T) ([]byte, error) { return Marshal(value) }
func (Codec[T]) Unmarshal(data []byte) (T, error) {
	proof, err := Prove[T](data)
	return proof.value, err
}
func (Codec[T]) MediaType() string { return MediaType }
