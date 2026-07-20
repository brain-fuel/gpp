# DAG-CBOR

`goforge.dev/goplus/std/dagcbor` implements the strict IPLD DAG-CBOR profile
for Go and Go+. It enforces string map keys, length-first ordering, minimal
integers and lengths, definite containers, finite 64-bit floats, one top-level
item, and tag 42 as the only tag.

The ordinary path is intentionally simple:

```go
data, err := dagcbor.Marshal(value)
err = dagcbor.Unmarshal(data, &value)
```

At trust boundaries, ask for proof instead:

```go
proof, err := dagcbor.Prove[Document](untrusted)
if err != nil {
	return err
}
document := proof.Value()
canonicalBytes := proof.Bytes()
contentDigest := proof.Digest()
```

`Proof[T]` cannot be constructed outside the package. It witnesses that the
complete input is the unique canonical DAG-CBOR representation of `T`; its
bytes are defensively copied and its digest is bound to those bytes.

For serde-polymorphic code, `dagcbor.Codec[T]{}` implements
`serde.Codec[T]`. `dagcbor.Link` represents a CID and handles the required tag
42 and `0x00` identity prefix automatically.
