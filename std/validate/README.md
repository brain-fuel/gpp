# validate

`validate` is a Go+-authored typed validation algebra. Successful validation
returns `Validated[T,p]`, retaining the exact predicate as an erased index and a
sealed runtime witness for ordinary Go callers. Atomic rules compose through
ordered conjunction, and typed field projections preserve machine-readable
failure paths.

The semantic and compatibility contract is in
[`../../spec/validate-design.md`](../../spec/validate-design.md).

This package is independently structured. Compatibility tests and the external
adapter target `github.com/go-playground/validator/v10` v10.30.3, distributed
under the MIT license; see `LICENSE` for the preserved notice.
