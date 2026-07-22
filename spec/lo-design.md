# Collection algebra and dependent-shape design

## Baseline and boundary

The compatibility baseline is `github.com/samber/lo` v1.53.0 at commit
`cf6fb4f9b08c1d3d6e309581316f106dc30b458e` (MIT). Its root module exposes 651
unique exported declarations across the root, iterator, mutable, and parallel
packages. `goforge.dev/lo/API_MANIFEST.csv` inventories each declaration and
assigns an explicit status.

The standard library does not mirror that helper surface. The compatibility
module owns migration names and historical behavior. Only independently useful
semantic structures are promoted:

- `std/nonempty` is consumed by `std/algebra` and `goforge.dev/lo`;
- the pre-existing `std/vec` gains equal-shape zip and bounded indexing.

## Semantic laws and effects

- `NonEmpty[T]` has private representation and owned storage. Construction
  copies input; `Head`, `Last`, and `Reduce1` are total.
- `Map` preserves order and non-emptiness. `Append` is associative and returns
  owned storage.
- `Vec[T,n]` encodes length. `Map` preserves `n`; `Zip` accepts two `Vec`s at
  the same `n`; `At` requires `Fin[n]`.
- Compatibility operations document whether they allocate, share, or mutate.
  Semantic `Into` functions expose reuse explicitly rather than depending on
  hidden pooling. Stable operations retain encounter order; map order is named
  as unspecified.
- Partial observations have `Option`/`Result` alternatives. Nonempty reduction
  has no fabricated identity and no empty-input panic.

## Dependent compiler work

Dependent call checking now recovers result indices from GADT constructors as
well as dependent functions. It recursively reconstructs constructor field
indices before erasure, retains those facts for single-assignment locals, and
prevents fixpoint lowering from discarding a producer involved in a mismatch.

Indexed constructors may introduce hidden naturals. These are existential at
the constructor boundary: `Succ(Zero()) : Fin[n+2]` can satisfy `Fin[2]` with
`n=0`, but cannot satisfy `Fin[1]`. A sound affine-natural solver handles this
constructor-local case. Caller parameters are never treated existentially;
their equalities still require universal proof through the normal decider.

## Completion evidence

Completion requires the exhaustive manifest, differential compatibility
corpus, collection laws, alias/order tests, two independent `std/nonempty`
consumers, positive and negative cross-package dependent fixtures, plain-Go
guards, race and fuzz runs, reproducible generation, full root/std/module tests,
vet, and paired performance evidence exceeding 2x speed and 50% allocation
reduction.
