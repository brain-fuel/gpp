# `std/validate` semantic and dependent-witness design

## Upstream baseline

The compatibility baseline is `github.com/go-playground/validator/v10` at
`v10.30.3` (MIT, tag commit `ac4c1bab0d4aa957466faa1948af28130767e43a`).
The Go+ package is independently structured. A separate compatibility adapter
owns reflection, struct tags, translations, and the upstream-shaped API.

## Semantic core

`std/validate` is a small typed validation algebra:

- `Predicate` is retained first-order witness data. At the type level, atoms use
  even natural IDs and ordered conjunctions use odd Cantor-pair IDs, giving
  `Named(id)` and `Both(p,q)` collision-free identities without hashes.
- `Rule[T,p]` is an immutable executable rule whose runtime predicate witness
  is `p` and whose failure output is structured.
- `Validated[T,p]` seals a value together with the rule and predicate that
  established `p`. Only successful validation can construct it.
- `Outcome[T,p]` is exhaustive: `Accepted(Validated[T,p])` or
  `Rejected(Failures)`.
- `Path[T,V]` projects a typed field. `At(path, rule)` retains the rule's
  predicate while prefixing failures with the typed path.
- `And` evaluates both rules in declaration order and returns
  `Rule[T,Both(p,q)]`. Failure order is stable.
- `Map` is deliberately revalidating in this stage. An arbitrary Go function
  is not a proof that it preserves `p`; the future proposition layer may add a
  proof-taking zero-revalidation operation.

There are no global registries or ambient translation state. Rules are safe for
concurrent reuse after construction. Failure trees are represented as a flat,
stable slice at the Go ABI because that is cheaper and easier to integrate; the
dependent proposition tree remains in `Predicate`.

## Erasure and plain-Go safety

Go+ erases `Rule[T,p]`, `Validated[T,p]`, and `Outcome[T,p]` indices while
generated values retain a sealed `Predicate` witness. Operations whose Go+
signatures require the same `p` compare witnesses at runtime so ordinary Go
cannot combine values established by different rules. Exported constructors
validate predicate IDs and paths. Proof-carrying variants are private.

## Compatibility boundary

The GoForge adapter supports a published matrix rather than claiming all v10
behavior. Its first compatibility tier covers:

- `required`, `omitempty`, `len`, `min`, `max`;
- `eq`, `ne`, `gt`, `gte`, `lt`, `lte`;
- `oneof`, `email`, `url`, `uuid`;
- `dive` for slices/arrays and nested structs;
- JSON-name field namespaces and stable declaration-order failures.

Unsupported or malformed tags are construction errors, never panics. Cross-
field tags, translations, aliases, maps-with-keys, filesystem/network probes,
and locale-specific identifiers remain later compatibility tiers.

## Performance gates

Benchmarks pin equivalent cached workloads against validator v10.30.3:

1. atomic field success;
2. atomic field failure;
3. simple cached struct success;
4. simple cached struct failure.

The paired core operation is `Check`, which returns stable structured failures
or nil just as upstream returns `ValidationErrors` or nil. `Validate` additionally
constructs a proof-bearing outcome and is reported separately.

For the typed semantic core, every paired workload must run at least twice as
fast and use no more than half the upstream allocations. An upstream zero-
allocation path therefore requires zero allocations. The reflection adapter is
reported separately and may not be used to claim the semantic-core speedup.

## Completion evidence

Completion requires the matrix and namespace corpus, core laws, config
integration, cross-package positive and negative dependent fixtures, Go-boundary
witness mismatch tests, race tests, fuzzing, generated-source reproducibility,
coverage, comparative benchmarks, vet, and full root/std test suites.
