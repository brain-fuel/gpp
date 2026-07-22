# decimal

`decimal` is the Go+-authored arbitrary-precision base-10 package. Source lives
in `decimal.gp`; generated `decimal_gp.go` is the stable plain-Go API.

The design intentionally separates three questions which older decimal APIs
often conflate:

1. `Decimal` represents an exact coefficient and exponent.
2. `RoundingMode` states how a lossy operation chooses a result.
3. `DivisionResult` states whether division was exact, rounded, or impossible.

`Fixed[p]` is the dependent API. The non-negative fractional-place count `p`
is checked by Go+ and erased from generated Go. `Quantize` is a boundary at
which rounding occurs; addition and subtraction preserve a common scale,
multiplication returns `Fixed[p+q]`, and rescaling names the new scale and
rounding mode explicitly.

```go
a := decimal.Quantize(2, decimal.RequireFromString("1.23"), decimal.HalfEven{})
b := decimal.Quantize(3, decimal.RequireFromString("4.567"), decimal.HalfEven{})
p := decimal.MulFixed(2, 3, a, b) // Fixed[5]
c := decimal.RescaleFixed(5, 2, p, decimal.HalfEven{}) // Fixed[2]
```

## Provenance

The compatibility target and differential oracle is
`github.com/shopspring/decimal` v1.4.0, Copyright (c) 2015 Spring, Inc., under
the MIT License. This implementation is independently structured and does not
copy its source. Compatible behavior, documentation comparisons, or imported
test vectors must retain that attribution.

This package is distributed under the package-local MIT License.
