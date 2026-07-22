# Performance baseline

The compatibility benchmark deliberately adds operands with very different
exponents, exercising coefficient copying and rescaling rather than a trivial
same-scale fast path.

Run on 2026-07-20 with Go 1.26.5, darwin/arm64, Apple M5 Max. The initial
implementation established this baseline:

```text
go test ./decimal -run '^$' -bench 'BenchmarkAdd$|BenchmarkAddUpstream$' \
  -benchmem -count=5 -benchtime=300ms

BenchmarkAdd              134.8–135.4 ns/op   352 B/op  10 allocs/op
BenchmarkAddUpstream      110.3–110.4 ns/op   280 B/op   7 allocs/op
```

After separating defensive public coefficient copies from internal read-only
operands and adding a bounded immutable power-of-ten table, an isolated ten-run
sample produced:

```text
BenchmarkAdd              51.2–51.8 ns/op    192 B/op   4 allocs/op
BenchmarkAddUpstream      111.7–112.2 ns/op  280 B/op   7 allocs/op
```

That is about 2.6 times faster than the original Go+ implementation and reduces
heap allocations by 60%. It is also about 2.1 times faster than the comparison
library on this deliberately difficult addition workload. `TestAddAllocationBudget`
guards the four-allocation ceiling. Zero allocations would require either
caller-provided storage or an inline small-coefficient representation; both are
larger API/representation changes and are not justified by this benchmark.
