package dagcbor

import (
	"bytes"
	"encoding/hex"
	"math"
	"testing"

	"goforge.dev/goplus/std/serde"
)

func TestIPLDCrossCodecFixtures(t *testing.T) {
	// Published IPLD cross-codec fixtures. Validation plus byte-for-byte
	// remarshal checks both the accepted data model and canonical form.
	for _, encoded := range []string{
		"8102",
		"8403040506",
		"8265617272617982626f66820582666e657374656482666172726179736121",
		"41a1",
		"d82a4a00015500050001020304",
		"d82a582300122022ad631c69ee983095b5b8acd029ff94aff1dc6c48837878589a92b90dfea317",
	} {
		data, err := hex.DecodeString(encoded)
		if err != nil {
			t.Fatal(err)
		}
		proof, err := Prove[any](data)
		if err != nil {
			t.Fatalf("Prove(%s): %v", encoded, err)
		}
		if !bytes.Equal(proof.Bytes(), data) {
			t.Fatalf("fixture changed: %x", proof.Bytes())
		}
	}
}

func TestCanonicalMapAndProof(t *testing.T) {
	type document struct {
		Long string `cbor:"long"`
		A    int    `cbor:"a"`
	}
	want := document{Long: "value", A: 1}
	proof, err := MarshalProved(want)
	if err != nil {
		t.Fatal(err)
	}
	if got := proof.Bytes(); len(got) == 0 || got[0] != 0xa2 {
		t.Fatalf("bytes = %x", got)
	}
	verified, err := Prove[document](proof.Bytes())
	if err != nil || verified.Value() != want || verified.Digest() != proof.Digest() {
		t.Fatalf("proof round trip = %#v, %v", verified.Value(), err)
	}
	copyOfBytes := proof.Bytes()
	copyOfBytes[0] = 0
	if bytes.Equal(copyOfBytes, proof.Bytes()) {
		t.Fatal("Proof.Bytes exposed mutable proof state")
	}
}

func TestTypedSerdeCodec(t *testing.T) {
	codec := Codec[map[string]int]{}
	want := map[string]int{"answer": 42}
	data, err := serde.Marshal[map[string]int](codec, want)
	if err != nil {
		t.Fatal(err)
	}
	got, err := serde.Unmarshal[map[string]int](codec, data)
	if err != nil || got["answer"] != 42 {
		t.Fatalf("round trip = %#v, %v", got, err)
	}
}

func TestLinkTag42RoundTrip(t *testing.T) {
	want := Link{1, 0x55, 0x12, 0x20, 1, 2, 3}
	data, err := Marshal(want)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.HasPrefix(data, []byte{0xd8, 0x2a}) {
		t.Fatalf("link = %x", data)
	}
	var got Link
	if err := Unmarshal(data, &got); err != nil || !bytes.Equal(got, want) {
		t.Fatalf("link round trip = %x, %v", got, err)
	}
}

func TestRejectsNonDAGCBOR(t *testing.T) {
	tests := [][]byte{
		{0xbf, 0x61, 'a', 0x01, 0xff},                 // indefinite map
		{0xa1, 0x01, 0x02},                            // integer map key
		{0xc0, 0x61, 'x'},                             // tag other than 42
		{0xf9, 0x7e, 0x00},                            // NaN
		{0x18, 0x01},                                  // non-minimal integer
		{0xa2, 0x62, 'a', 'a', 0x01, 0x61, 'b', 0x02}, // wrong key order
		{0x01, 0x02},                                  // trailing item
	}
	for _, data := range tests {
		if err := Validate(data); err == nil {
			t.Fatalf("Validate(%x) succeeded", data)
		}
	}
	if _, err := Marshal(math.Inf(1)); err == nil {
		t.Fatal("Marshal(+Inf) succeeded")
	}
}

func TestProofRejectsLossyTypedDecode(t *testing.T) {
	type onlyA struct {
		A int `cbor:"a"`
	}
	data, err := Marshal(map[string]int{"a": 1, "extra": 2})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := Prove[onlyA](data); err == nil {
		t.Fatal("Prove accepted a decode that discarded an unknown field")
	}
}
