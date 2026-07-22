# Go+ decimal design and compatibility contract

This document is normative for `std/decimal`.

## Representation

`Decimal` denotes `coefficient * 10^exponent`, where the coefficient is an
arbitrary-precision signed integer and the exponent is an `int32`. Values are
immutable: constructors and accessors copy `big.Int`. The zero Go value denotes
zero. Representation equality is not numeric equality; `Equal` and `Cmp`
rescale before comparing.

`String` is canonical numeric text. It does not preserve insignificant trailing
zeroes. Binary encoding does preserve coefficient and exponent.

## Loss and failure

Exact operations (`Add`, `Sub`, `Mul`, `Cmp`) do not accept a context and never
round. `Round` names one of six exhaustive modes. Public rounding and formatting
use a bounded `Scale`; `Divide` requires a positive, bounded `Precision` and
returns `Exact`, `Rounded`, or `DivisionByZero`. Generated Go guards both
refinements, preventing untrusted callers from requesting pathological powers
of ten. Division does not hide division-by-zero behind a panic and does not use
mutable package-global precision.

JSON is quoted by default because an unquoted JSON number is commonly decoded
through binary64. SQL values use canonical decimal strings.

## Dependent surface

`Fixed[p]` carries a non-negative number of fractional places in the Go+ type.
The index erases in generated Go. `Quantize(p, d, mode)` is a rounding boundary.
`AddFixed` and `SubFixed` require equal indices, `MulFixed` produces
`Fixed[p+q]`, and `RescaleFixed` is the explicit lossy transition to a new
index. Cross-package marker reconstruction must reject `Fixed[2] + Fixed[3]`
and normalize arithmetic such as `2+3 = 5`.

Erasure does not discard the runtime boundary witness. The sealed concrete
representation retains its place count, allowing generated plain Go to reject
an equal-scale operation when callers pass values created at different scales.
Go callers cannot construct the sealed representation directly.

Existential parsing remains future work: parsing a scale from input should
produce a package containing `p` and `Fixed[p]`, rather than forge a statically
chosen index.

## Compatibility target

The behavioral oracle is `github.com/shopspring/decimal` v1.4.0 for parsing,
canonical formatting, exact arithmetic, comparisons, and compatible
serialization operations. Go+ deliberately differs where semantics improve:

- rounding is an explicit enum rather than several method names;
- division precision is an argument, not mutable global state;
- division by zero is an exhaustive result;
- fixed scale can be carried as an erased type index;
- JSON always defaults to the precision-safe quoted form.
- parsing uses conventional sign placement and deliberately rejects permissive
  oddities such as `.+1` which the compatibility target happens to accept.

API parity is staged. Transcendentals, powers, cash rounding, nullable decimal,
float construction, and aggregate helpers are not part of the first core and
must not be claimed as compatible until differential tests land.

## Completion evidence

The full goal requires:

1. Go+-authored source and reproducible generated Go.
2. Exact arithmetic, explicit rounding/division semantics, and immutable
   arbitrary-precision representation.
3. Text, JSON, binary, Gob, and database integration.
4. Differential parsing/arithmetic/rounding/serialization tests against the
   compatibility target.
5. Algebraic property tests, fuzzing, race tests, and comparative benchmarks.
6. A cross-package dependent test proving equal-scale acceptance and
   mixed-scale rejection.
7. Plain-Go boundary tests for refinement and index guards.
8. Attribution of every upstream-derived source, fixture, or document.
9. Full root and std tests, vet, generated-output verification, and
   `git diff --check`.
