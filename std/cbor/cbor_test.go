package cbor

import (
	"bytes"
	"encoding/hex"
	"io"
	"testing"

	"goforge.dev/goplus/std/serde"
)

func TestRFC8949AppendixVectors(t *testing.T) {
	tests := []struct {
		hex   string
		value any
	}{
		{"00", uint64(0)},
		{"1818", uint64(24)},
		{"20", int64(-1)},
		{"6161", "a"},
		{"83010203", []any{uint64(1), uint64(2), uint64(3)}},
		{"a26161016162820203", map[string]any{"a": uint64(1), "b": []any{uint64(2), uint64(3)}}},
	}
	for _, test := range tests {
		data, _ := hex.DecodeString(test.hex)
		var got any
		if err := Unmarshal(data, &got); err != nil {
			t.Fatalf("Unmarshal(%s): %v", test.hex, err)
		}
		encoded, err := Marshal(got)
		if err != nil {
			t.Fatalf("Marshal(%s): %v", test.hex, err)
		}
		if !bytes.Equal(encoded, data) {
			t.Fatalf("round trip %s = %x", test.hex, encoded)
		}
	}
}

func TestStreamingAndDiagnosticNotation(t *testing.T) {
	var stream bytes.Buffer
	encoder := NewEncoder(&stream)
	if err := encoder.Encode("first"); err != nil {
		t.Fatal(err)
	}
	if err := encoder.Encode(uint64(2)); err != nil {
		t.Fatal(err)
	}
	decoder := NewDecoder(&stream)
	var first string
	var second uint64
	if err := decoder.Decode(&first); err != nil {
		t.Fatal(err)
	}
	if err := decoder.Decode(&second); err != nil {
		t.Fatal(err)
	}
	if err := decoder.Decode(new(any)); err != io.EOF {
		t.Fatalf("end of sequence = %v", err)
	}
	if first != "first" || second != 2 {
		t.Fatalf("sequence = %q, %d", first, second)
	}
	diagnostic, err := Diagnose([]byte{0x82, 0x01, 0x02})
	if err != nil || diagnostic != "[1, 2]" {
		t.Fatalf("diagnostic = %q, %v", diagnostic, err)
	}
}

func TestTypedSerdeCodec(t *testing.T) {
	type message struct {
		Name string `cbor:"name"`
		N    int    `cbor:"n"`
	}
	want := message{Name: "accessible", N: 3}
	codec := Codec[message]{}
	data, err := serde.Marshal[message](codec, want)
	if err != nil {
		t.Fatal(err)
	}
	got, err := serde.Unmarshal[message](codec, data)
	if err != nil || got != want {
		t.Fatalf("round trip = %#v, %v", got, err)
	}
}

func TestRejectsDuplicateMapKeysAndTrailingItems(t *testing.T) {
	for _, data := range [][]byte{
		{0xa2, 0x61, 'a', 0x01, 0x61, 'a', 0x02},
		{0x01, 0x02},
	} {
		if err := Valid(data); err == nil {
			t.Fatalf("Valid(%x) succeeded", data)
		}
	}
}
