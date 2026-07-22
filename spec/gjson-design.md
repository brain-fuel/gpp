# `/goals/07-gjson`: schema-aware paths and borrowed values

## Placement and provenance

The rewrite lives in sibling module `goforge.dev/gjson`. It pins
`github.com/tidwall/gjson` v1.19.0 at
`0fac2c9aa6eb5d5564bfaaaad513ce0d5d2314de` and retains Josh Baker's MIT
notice. Path syntax policy and a compatibility facade do not belong in `std`.
The typed path abstraction remains outside `std/serde/path` until JSON, CBOR,
and another format demonstrate the same composition and lookup laws.

## Semantic split

`CompilePath` parses the bounded tier once. `ParseDocument` validates a complete
JSON value and builds an immutable structural index. Repeated queries return a
`Borrowed` view into the retained source string. Missing, explicit null,
present, and malformed states are distinct. Raw decimal spelling is retained;
integer access rejects fractions and overflow, while float conversion is an
explicit lossy operation.

Byte input is copied once. This avoids an unsafe string alias whose lifetime
could be invalidated by caller mutation. Escaped strings decode with
`AppendString(dst)` into reusable caller-owned storage. `LineScanner` owns one
JSON-lines record at a time and publishes independently retainable documents.

Modifiers are held by immutable `Registry` snapshots. No package-global flag or
registry affects query semantics.

## Dependent core

The Go+-authored core in `gjson/typed/typed.gp` defines:

```go
type Path[S nat, T any] enum { /* sealed representation */ }

type TypedDocument[S nat, D any] enum { /* retained schema + payload */ }

type Lookup[T any, p nat] enum {
    Missing() Lookup[T, 0]
    Null() Lookup[T, 1]
    Present(value T) Lookup[T, 2]
    Malformed(error PathError) Lookup[T, 3]
}
```

`SomePath[S]` hides the leaf `T` for runtime path strings while retaining the
schema identity; exhaustive matching recovers boolean, integer, number-text, or
borrowed-string paths. `PathParse[S]` keeps parse rejection explicit. `PresentValue`
accepts only `Lookup[T,2]`, and `Compose` preserves `S` while changing the leaf
type to that of the suffix.

JSON and CBOR payloads are bound as `TypedDocument[S,D]`. Every lookup requires
the same `S` on its path and document; retained runtime witnesses recheck that
relationship after ordinary-Go erasure. `LookupStringInto` is an unboxed
eliminator for the performance-sensitive borrowed `StringView` path while the
generic `SomeLookup` remains the proof-oriented exhaustive boundary.

Cross-package fixtures prove a schema-matched path/document pair is accepted,
reject use of a `Path[9,int]` as `Path[10,int]`, reject a schema-10 document
against a schema-9 path, and reject passing `Lookup[T,0]` to the presence-only
eliminator. Runtime schema IDs remain in sealed generated values for
ordinary-Go boundary defense.

## Multiple format consumers

`LookupInteger` is the JSON consumer. `LookupCBORInteger` traverses RFC 8949
data through `std/cbor` using the same `Path[S,int]`. A test constructs one path
and proves equal results from JSON and CBOR documents. This is evidence for a
future shared abstraction, but one scalar operation is not sufficient to
promote a standard package.

## Gate evidence

- a 45-declaration pinned API inventory and explicit path matrix;
- upstream differential path/result corpus and fuzzing of the shared tier;
- malformed JSON fuzzing against upstream validity;
- borrowed lifetime, byte ownership, lossless number, streaming, immutable
  registry, race, and positive/negative dependent tests;
- generated-source and manifest reproducibility, tidy/vet, and full root/std
  suites;
- a five-run repeated escaped-string query gate requiring at least 2x speed and
  50% fewer allocations than GJSON v1.19.0.
