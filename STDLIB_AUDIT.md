# Standard-library audit: Quicken and Assayxport

This audit records the abstraction review performed while rewriting Quicken
and Assayxport in Go+. The result is the null set: neither application contains
a new abstraction mature enough for `goforge.dev/goplus/std`.

## Quicken

- `SessionStore` and its in-memory implementation encode Quicken's
  `LiveSession` identity and lifecycle. A generic concurrent map would erase
  the useful domain contract, while `std/guarded` and `std/deepmap` already
  provide the reusable ownership primitives below it.
- `LiveChannel`, long polling, WebSocket framing, markup rendering, and page
  regions are HTTP/UI protocol machinery, not language-level building blocks.
- `ServeOption` is the ordinary functional-options pattern and needs no shared
  package.

## Assayxport

- Extractor interfaces describe Assayxport's schema and progressive extraction
  protocol. They are extension points for that application, not general
  iteration interfaces.
- The loader scheduler and byte-budget cache are coupled: priorities come from
  viewport intent, pins protect visible shards, and eviction returns shard IDs
  for graph cleanup. Extracting a generic priority queue or LRU would discard
  those invariants; a second independent consumer should precede promotion.
- Hierarchy `Summary.Plus` is a useful monoid, but its fields and reconciliation
  rules are assay-specific. `std/algebra` already supplies the reusable
  algebraic vocabulary.
- Tree-sitter wrappers, graph indexes, layout, schema, and manifest streaming
  are all domain adapters.

## Promotion rule

Promote a future candidate only when at least two independent consumers share
the same API and laws without domain-shaped type parameters or callbacks. This
keeps `std` small and prevents an application implementation detail from
becoming a compatibility promise.
