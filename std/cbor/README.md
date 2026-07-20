# CBOR

`goforge.dev/goplus/std/cbor` is the Go and Go+ entry point for RFC 8949 CBOR.
The default is deterministic because stable bytes are less surprising for
hashes, signatures, caches, tests, and cross-language interchange:

```go
data, err := cbor.Marshal(value)
err = cbor.Unmarshal(data, &value)
```

The typed `cbor.Codec[T]{}` implements `serde.Codec[T]`:

```go
codec := cbor.Codec[Message]{}
data, err := serde.Marshal(codec, message)
message, err = serde.Unmarshal(codec, data)
```

`LegacyCodec[T]` emits RFC 7049 canonical ordering for protocols that require
that historical profile. RFC 8949 did not introduce a new wire format, so both
codecs use the same safe decoder. The decoder accepts definite and indefinite
RFC 8949 items, rejects duplicate map keys and invalid UTF-8, applies bounded
nested/container limits, and requires exactly one top-level item.

`NewEncoder` and `NewDecoder` handle CBOR sequences. `UnmarshalFirst` exposes
the remaining sequence bytes, and `Diagnose` renders RFC 8949 diagnostic
notation. `Tag`, `RawTag`, `RawMessage`, `SimpleValue`, `Marshaler`, and
`Unmarshaler` cover CBOR-based protocols without requiring a second import.
