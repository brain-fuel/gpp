# Go+ rewrite goals

This is the authoritative index for `/goals/01` through `/goals/10`. Rankings
were refreshed on 2026-07-20. GitHub stars are recorded only as a reproducible
adoption proxy; compatibility imports and downstream consumers are stronger
evidence when available.

The ranking weights three questions in order: likely users helped, reusable
Go+ standard-library value, and whether Go+ can give the rewrite materially
better semantics than ordinary Go. Every source project is MIT-licensed. A
rewrite must retain the upstream copyright and license, identify its pinned
compatibility baseline, and distinguish copied/adapted code from independently
structured code.

## Candidate evidence snapshot

| Goal | Upstream | Adoption proxy | License |
|---|---|---:|---|
| 01 | [shopspring/decimal](https://github.com/shopspring/decimal) | 7.5k stars | MIT |
| 02 | [go-playground/validator](https://github.com/go-playground/validator) | 20.1k stars | MIT |
| 03 | [samber/lo](https://github.com/samber/lo) | 21.4k stars | MIT |
| 04 | [spf13/viper](https://github.com/spf13/viper) | 30.4k stars | MIT |
| 05 | [go-chi/chi](https://github.com/go-chi/chi) | 22.6k stars | MIT |
| 06 | [expr-lang/expr](https://github.com/expr-lang/expr) | 8.0k stars | MIT |
| 07 | [tidwall/gjson](https://github.com/tidwall/gjson) | 15.6k stars | MIT |
| 08 | [robfig/cron](https://github.com/robfig/cron) | 14.2k stars | MIT |
| 09 | [go-resty/resty](https://github.com/go-resty/resty) | 11.8k stars | MIT |
| 10 | [alecthomas/participle](https://github.com/alecthomas/participle) | 3.9k stars | MIT |

Counts are rounded snapshots, not ranking scores. The order deliberately moves
semantic forcing cases above some larger repositories.

## Goals

### `/goals/01-decimal` - `shopspring/decimal` -> `std/decimal` (complete)

- **Why first:** Exact money and measurement arithmetic has broad application,
  and global/default rounding policies are a good target for explicit sums.
- **Go+ result:** Immutable decimal values, explicit rounding modes and division
  outcomes, refinement-checked precision/scale, and `Fixed[p]` arithmetic.
- **Dependent pressure:** Index arithmetic (`p+q`), cross-package index recovery,
  and retained runtime witnesses at erased Go boundaries.
- **Gate:** Compatibility/differential corpus, 100% statement coverage, race and
  fuzz testing, generated-source check, and performance/allocation parity.
- **Status:** implemented in `std/decimal`.

### `/goals/02-validator` - `go-playground/validator` -> `std/validate` (complete)

- **Why second:** Roughly 20k GitHub stars, widespread web/API use, and the
  default validation engine used by Gin make successful migration unusually
  valuable. Its tag-and-reflection API currently forgets validation after the
  call returns.
- **Destination:** A small Go+-authored `std/validate` core with a compatibility
  adapter in a GoForge module. Do not put translations, every baked-in format,
  or reflection cache policy into `std` initially.
- **Semantic rewrite:** `Rule[T]`, exhaustive structured failure trees, rule
  composition with laws, typed field paths, and `Validated[T, P]` witnesses.
  Existing struct tags remain an adapter, not the semantic center.
- **Dependent pressure:** Predicate-indexed witnesses, conjunction of predicates,
  proof-preserving `Map`, and safe erasure/runtime revalidation for ordinary Go.
- **Gate:** Pin validator v10; publish an explicit supported-tag matrix; match its
  success/failure corpus and namespace behavior; integrate with `std/config`;
  prove composition laws; benchmark cached success and failure paths; compile
  cross-package accept/reject examples for `Validated[T, P]`.
- **Status:** implemented in `std/validate`, with the reflection/tag migration
  adapter in sibling module `goforge.dev/validator`. Paired core workloads are
  3.6x–7.8x faster than v10.30.3; allocating failure paths use 1 vs 3 and 2 vs
  7 allocations, while both success paths remain allocation-free.

### `/goals/03-lo` - `samber/lo` -> GoForge collection algebra (complete)

- **Why third:** Roughly 21k stars and a very broad generic-programming audience.
  A literal helper-for-helper clone would bloat `std`, but a rewrite can expose
  the algebra hidden behind the popular API.
- **Destination:** A GoForge compatibility package. Promote only independently
  reused primitives to `std/option`, `std/result`, `std/algebra`, or a narrowly
  scoped `std/nonempty` package.
- **Semantic rewrite:** Total variants for partial helpers, explicit `Option` and
  `Result`, lawful folds/traversals, stable versus unordered operations, and no
  panic-based indexing in the semantic API.
- **Dependent pressure:** `NonEmpty[T]`, length-indexed arrays/vectors, shape-
  preserving map, equal-length zip, and bounds-proven indexing.
- **Gate:** API inventory and parity manifest, differential/property corpus,
  order and aliasing guarantees, zero-surprise allocation benchmarks, and at
  least two consumers before any new standard package is promoted.
- **Status:** implemented as sibling module `goforge.dev/lo`, with 47 compatible
  declarations and an explicit 651-declaration upstream inventory. The fused
  `FilterMapInto` semantic API is at least 2.51x faster than upstream
  `FilterMap` in the recorded five-run gate and uses 0 instead of 1 allocation;
  compatibility `Map` retains upstream allocation parity. `std/nonempty` and
  the dependent `Vec[T,n]`/`Fin[n]` extensions have two independent consumers.

### `/goals/04-viper` - `spf13/viper` -> typed GoForge config over `std/config` (complete)

- **Why fourth:** Roughly 30k stars and enormous downstream reach. It is ranked
  below smaller projects because cloning its mutable global/reflection-heavy API
  would preserve the semantics Go+ should improve.
- **Destination:** A GoForge compatibility facade built on `std/config`; only
  source precedence, provenance, decoding contracts, and schema primitives
  belong in the standard library.
- **Semantic rewrite:** Immutable snapshots, exhaustive source provenance,
  deterministic precedence, typed keys, explicit missing/decode errors, and a
  separate effectful reload stream.
- **Dependent pressure:** `Config[S]` schema indices, `Key[S, T]`, proof that
  required keys exist after validation, and typed subset projection.
- **Gate:** Pin a Viper release and precedence behavior; compatibility tests for
  defaults/files/env/flags/aliases; deterministic merge laws; config integration
  tests; race tests for reload; migration examples without package globals.
- **Status:** implemented as sibling module `goforge.dev/viper`, pinned to
  v1.21.0 (`394040caccbdf5821fa6839386a35f0fb1b1ee9e`). Its reproducible
  192-declaration inventory marks 63 high-use declarations compatible and 129
  explicitly deferred. `std/config` now supplies provenance-retaining
  `Snapshot[s]`, `Key[T,s]`, required-key evidence, and `Subset[s,sub]` typed
  projection; a race-tested `ReloadStream` publishes ordered immutable success
  or failure events outside the read path. The immutable snapshot read is
  8.62x faster than upstream `GetString` in the recorded five-run gate and uses
  0 rather than 3 allocations.

### `/goals/05-chi` - `go-chi/chi` -> typed GoForge router over `std/http` (complete)

- **Why fifth:** Roughly 22.5k stars, no external dependencies, and direct
  `net/http` compatibility give it a large audience and a clean rewrite seam.
- **Destination:** GoForge first. Donate route-pattern parsing and typed parameter
  primitives to `std/http` only after a second router/server consumer appears.
- **Semantic rewrite:** An immutable route tree, exhaustive match outcomes,
  explicit middleware capabilities, conflict detection, and generated OpenAPI-
  usable route metadata without runtime tree introspection.
- **Dependent pressure:** singleton route patterns, parameter environments,
  handlers whose argument record is derived from the pattern, and route-set
  indices preventing duplicate/conflicting registration.
- **Gate:** Chi routing/middleware corpus, `net/http` interoperability, ambiguity
  diagnostics, fuzzed pattern parsing, benchmark parity, and compile-time tests
  for missing/extra route parameters.
- **Status:** implemented as sibling module `goforge.dev/chi`, pinned to v5.3.1
  (`8b258c7bb28f97a5f2a856ff7ef962578fec9215`). Its reproducible
  178-declaration inventory marks 53 root declarations compatible, 26 other
  declarations deferred, and 99 middleware declarations deferred to a
  capability-typed tier. `std/http/route` now supplies `Pattern[p]`,
  `Request[p]`, `ParamKey[T,p]`, sealed `Handler[p]`, indexed route sets, and
  capability-indexed middleware, with retained erased-boundary witnesses;
  `goforge.dev/chi` and `std/http.RouteHandler` are its two production
  consumers. The immutable exact-route snapshot is 5.63x faster than upstream
  Chi in the recorded five-run gate and uses 0 rather than 2 allocations.

### `/goals/06-expr` - `expr-lang/expr` -> typed GoForge expression engine

- **Why sixth:** Roughly 8k stars, but the strongest direct forcing case for
  GADTs and existential types. Dynamic expression evaluation benefits greatly
  from making result types and effects explicit.
- **Destination:** GoForge package; reusable typed-AST/elaboration machinery is
  compiler infrastructure, not a general-purpose standard package.
- **Semantic rewrite:** `Expr[T]` GADT, exhaustive typed bytecode instructions,
  explicit compile versus runtime failures, controlled effects, and no `any`
  in the checked evaluation path.
- **Dependent pressure:** existential `SomeExpr` returned by parsing, equality
  witnesses for type refinement, typed environments, and length-indexed stack
  effects for bytecode verification.
- **Gate:** Language/conformance matrix, differential parser/evaluator corpus,
  rejection corpus, bytecode stack-safety proof tests, fuzzing, and competitive
  compile/evaluate benchmarks.
- **Status:** implemented as sibling module `goforge.dev/expr`, pinned to
  v1.17.8 (`21f4f0575591d7097e576edd7983daf23c1e4afe`). Its reproducible
  inventory records all 617 exported upstream declarations and its language
  matrix explicitly bounds the checked tier. The Go+-authored core supplies
  `Expr[T]`, finite existential `SomeExpr`, explicit effects/failures, typed
  environments, `Instruction[input,output]`, `Stack[n]`, and `Eq[n,m]` depth
  transport. Imported positive/negative fixtures prove bytecode composition,
  reject underflow and wrong instruction effects, and reject false equality
  witnesses. Differential, rejection, fuzz, race, generation, root/std, and
  allocation gates pass. In the recorded five-run gate compilation is at least
  4.72x faster with 59.4% fewer allocations, while the typed scalar VM is at
  least 2.81x faster and uses 0 rather than 3 allocations; the `map[string]any`
  migration facade also uses zero allocations.

### `/goals/07-gjson` - `tidwall/gjson` -> schema-aware GoForge JSON paths

- **Why seventh:** Roughly 15.5k stars and pervasive JSON use. Raw dynamic lookup
  remains available, while schema-aware callers should not repeatedly inspect
  result kinds and presence flags.
- **Destination:** GoForge first; a small `std/serde/path` abstraction is eligible
  only when CBOR/DAG-CBOR and another format share its laws.
- **Semantic rewrite:** Parsed immutable paths, exhaustive missing/null/value/error
  results, lossless number policy, streaming traversal, and an explicit modifier
  registry rather than ambient globals.
- **Dependent pressure:** `Path[S, T]`, presence-indexed results, existential
  paths for runtime strings, and schema-preserving path composition.
- **Gate:** GJSON path compatibility matrix and corpus, malformed-input fuzzing,
  zero-copy lifetime documentation/tests, allocation and throughput parity, and
  typed JSON/CBOR consumer demonstrations.
- **Status:** implemented as sibling module `goforge.dev/gjson`, pinned to
  v1.19.0 (`0fac2c9aa6eb5d5564bfaaaad513ce0d5d2314de`). Its reproducible
  inventory records all 45 exported declarations: 26 compatible, three global
  modifier declarations replaced by immutable `Registry`, and 16 explicitly
  deferred. Validated immutable documents retain lossless number text and an
  index of borrowed values; byte input is owned, JSON-lines traversal streams,
  and escaped strings decode into reusable caller storage. The Go+-authored
  core supplies `Path[S,T]`, `TypedDocument[S,D]`, `Lookup[T,p]`, finite
  existential paths, presence-only elimination, and schema-preserving
  composition. Imported fixtures accept a matched path/document pair and
  reject wrong path schemas, wrong document schemas, and use of missing
  evidence as present; erased Go boundaries recheck retained schema IDs. One
  `Path[S,int]` is consumed by both JSON and `std/cbor`. Differential and
  malformed fuzzing, zero-copy lifetime/ownership, race, generation, root/std,
  and allocation gates pass. In the recorded five-run gate the schema-typed
  borrowed-string query is at least 2.31x faster than GJSON v1.19.0 and uses
  0 rather than 1 allocation (100% fewer).

### `/goals/08-cron` - `robfig/cron` -> `std/schedule` (complete)

- **Why eighth:** Roughly 14k stars and a stable, compact scheduling domain whose
  parser ambiguity and runtime lifecycle are well suited to explicit types.
- **Destination:** Start in GoForge; promote the schedule value/parser to
  `std/schedule`, leaving goroutine ownership and logging adapters outside.
- **Semantic rewrite:** Separate standard and seconds-enabled grammars, validated
  immutable schedules, exhaustive next-run outcomes, explicit overlap policy,
  and lifecycle typestate.
- **Dependent pressure:** grammar-indexed `Schedule[F]`, nonempty field sets,
  parser-produced existential schedules, and `Cron[Stopped|Running]` transitions.
- **Gate:** Robfig parser/next-time corpus including DST, fake-clock concurrency
  tests, overlap laws, race tests, and compile-time lifecycle misuse rejection.
- **Status:** implemented as the Go+-authored `std/schedule` core and sibling
  module `goforge.dev/cron`, pinned to v3.0.1
  (`ccba498c397bb90a9c84945bbb0f7af2d72b6309`). The core separates
  `Schedule[5]` and `Schedule[6]`, seals nonempty `FieldSet[d]`, returns finite
  existential parses and exhaustive next outcomes, and matches Robfig across
  standard/seconds syntax, descriptors, named fields, leap years, locations,
  and DST gaps/repeats. The runner requires explicit parallel/skip/delay policy
  and enforces `Cron[0|1]` lifecycle transitions across package boundaries;
  generated Go retains runtime guards. `goforge.dev/cron` and `std/workflow`
  are independent production consumers. Fake-clock, overlap-law, fuzz, race,
  generation, vet, std-wide, and positive/negative compile gates pass. In the
  recorded five-run parser gate the rewrite is at least 2.26x faster and uses
  7 rather than 27 allocations (74.1% fewer).

### `/goals/09-resty` - `go-resty/resty` -> typed GoForge HTTP client

- **Why ninth:** Roughly 11.7k stars and more than 20k reported dependents. It can
  consolidate `std/http`, `std/retry`, streaming, and effect-boundary design.
- **Destination:** GoForge compatibility/client package over existing Go+ std
  primitives; promote only protocol-neutral request/response state machinery.
- **Semantic rewrite:** Immutable client policy, request builder typestate,
  exhaustive transport/status/decode outcomes, replayability-aware retries,
  and owned streaming bodies.
- **Dependent pressure:** method/body/replayability indices, response-code sums,
  and transitions that prevent retrying non-replayable bodies or decoding twice.
- **Gate:** Pin Resty v2/v3 target explicitly, publish compatibility matrix,
  HTTP conformance and cancellation tests, leak/race tests, retry safety tests,
  and compile-time illegal-state rejection.

### `/goals/10-participle` - `alecthomas/participle` -> typed parser construction

- **Why tenth:** A smaller audience (roughly 3.9k stars), but an excellent final
  forcing function: grammars, token streams, captures, and AST construction tie
  together nearly every staged dependent feature.
- **Destination:** GoForge package interoperating with `std/parsec`; promote only
  shared lexer/span/error primitives demonstrated by both consumers.
- **Semantic rewrite:** Grammar AST as a GADT, exhaustive lexer/parser failures,
  immutable source spans, explicit lookahead/commit semantics, and generated
  parsers whose output type is tied to the grammar.
- **Dependent pressure:** `Parser[G, T]`, grammar composition with FIRST-set
  evidence, token-count/indexed spans, and existential packaging of dynamically
  loaded grammars.
- **Gate:** Participle grammar compatibility corpus, ambiguity diagnostics,
  parser laws, differential/fuzz tests, generated-Go inspection, and realistic
  language benchmarks.

## Package workflow

Each goal follows the same sequence:

1. Pin an upstream version; record MIT provenance, API inventory, behavioral
   corpus, adoption evidence, and known incompatibilities.
2. Choose the semantic core before compatibility work. Illegal states become
   enums, refinements, indices, or explicit effects rather than comments.
3. Implement in `.gp`; generated Go is a checked distribution artifact. Keep a
   plain-Go boundary with runtime validation corresponding to erased proofs.
4. Add upstream differential tests, algebraic/property tests, fuzzing, race
   tests, serialization/interoperability checks, and comparative benchmarks.
5. Exercise the dependent surface across package boundaries with positive and
   negative compile fixtures. No feature counts as shipped if it only works in
   the declaring file.
6. Integrate at least one real GoForge consumer. Promotion to `std` additionally
   requires a second independent consumer sharing the same API and laws.
7. Audit licenses, generated-source reproducibility, module tidiness, vet, full
   root/std tests, coverage, performance, and migration documentation.

## Dependent-typing roadmap

Go+ remains a strict source superset of Go by making every feature opt-in in
`.gp` files (or explicit declarations) and by erasing proofs/indices to ordinary
Go plus boundary checks. Ordinary `.go` behavior and Go's type checker remain
unchanged.

### Stage A - decidable indexed programming (shipped foundation)

Retain refinements, GADTs, natural-number/value indices, cross-package markers,
index arithmetic normalization, structural matches, and runtime witnesses at
Go boundaries. Finish robustness for aliases, reassignment, generic wrappers,
methods, interfaces, separate compilation, and diagnostics. Goals 01-03 are the
forcing consumers.

### Stage B - propositions and validated witnesses

Add an opt-in proposition kind, named predicate parameters, conjunction,
equality witnesses, proof-preserving functions, and explicit `assume` only at
foreign boundaries. Proof terms erase; generated Go rechecks exported inputs.
Keep inference decidable by limiting automatic discharge to constants, path
conditions, registered total functions, and an SMT-free arithmetic fragment.
Goal 02 is the primary acceptance test.

### Stage C - existential dependent pairs

Add `exists n. T[n]`/Sigma packaging and match-based witness recovery so parsing
runtime data can safely return a value whose index was not known statically.
Support equality transport and dependent pattern refinement without casts.
Goals 03, 06, 07, 08, and 10 require this stage.

### Stage D - a predictable index solver

Implement canonical normalization plus Presburger arithmetic for naturals and
integers, finite-set membership, singleton strings, and user-declared opaque
index functions with congruence only. Emit proof traces for diagnostics and
cache normalized imported contracts. Do not make arbitrary Go execution part
of type checking. Goals 03, 05, 06, 07, and 08 exercise these domains.

### Stage E - dependent functions and records

Generalize indexed declarations to Pi types, dependent records, schema/key
projection, implicit arguments, holes with actionable goals, and bidirectional
elaboration. Add row-like finite maps only after singleton strings and
existentials are stable. Goals 04, 05, 07, and 10 are the forcing consumers.

### Stage F - total dependent core

To accurately call Go+ dependently typed, add an opt-in kernel with universes,
Pi and Sigma types, inductive families, intensional equality/J, normalization,
positivity checking, and termination/productivity checking. Kernel checking
must be small and deterministic; elaboration and automation remain outside the
trusted core. `total func` supplies executable proofs, while ordinary Go
functions remain partial and cannot reduce during type checking.

### Stage G - Go interoperability and production hardening

Specify representation/erasure, dictionary and witness ABI stability, reflection
behavior, interface satisfaction, versioned package markers, proof-irrelevant
hashing, LSP goals/hover/completion, incremental checking, and resource limits.
Every exported dependent API must define what plain Go sees and where runtime
checks occur. Unsafe/foreign facts stay visibly labelled and auditable.

The stopping point after Stage E is a useful refinement/indexed language. Stage
F is the threshold for a genuine dependently typed language; claiming that term
before a checked Pi/Sigma/equality/inductive/normalizing core would overstate the
implementation.
