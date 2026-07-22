# `/goals/06-expr`: typed expressions and verified bytecode

## Placement

The rewrite lives in sibling module `goforge.dev/expr`, not `std`. Expression
language policy, compatibility syntax, optimization strategy, and effect
capabilities are application/compiler infrastructure rather than universal
standard-library contracts. No new `std` package is promoted by this goal.

The module pins `github.com/expr-lang/expr` v1.17.8 at
`21f4f0575591d7097e576edd7983daf23c1e4afe` and retains its MIT notice.

## Checked semantic core

The authoritative semantic model is authored in `expr/typed/typed.gp`:

```go
type Expr[T any] enum {
    Int(value int) Expr[int]
    Bool(value bool) Expr[bool]
    Add(left, right Expr[int]) Expr[int]
    If(condition Expr[bool], then, otherwise Expr[T])
    // variables, strings, unary operations, comparisons, equality, logic...
}

type SomeExpr enum {
    SomeInt(expression Expr[int])
    SomeBool(expression Expr[bool])
    SomeString(expression Expr[string])
}
```

`SomeExpr` is the finite existential boundary for the supported result
universe. Exhaustive matching recovers a concrete `T`; evaluation beyond that
point contains no dynamically typed value. `EvalResult[T]` makes runtime
failure explicit, and `EffectOf` classifies pure expressions versus environment
reads. The ordinary-Go parser is the erasure boundary and returns `SomeExpr`
through `ParseTyped`.

## Dependent bytecode contract

`Stack[n]` retains depth in its type and `Instruction[input,output]` states each
transition:

- literal and environment loads: `n -> n+1`;
- integer binary operations: `n+2 -> n+1`.

Executable interpreters cover both instruction families. Generated Go retains
defensive wrong-shape failures for foreign callers after erasure, while Go+
callers cannot construct an underflowing composition. `TransportStack` accepts
an erased `Eq[n,m]` proof, making normalized depth equality explicit without a
runtime representation change.

Cross-package compiler fixtures establish all three important cases:

1. `0 -> 1 -> 2 -> 1` composition is accepted from another module;
2. applying an `n+2 -> n+1` operation to `Stack[0]` is rejected;
3. `refl` cannot transport `Stack[1]` to `Stack[2]`.

This exercises existing GADT refinement, natural indices, arithmetic
normalization, imported dependent markers, equality witnesses, erasure, and
diagnostics. A native unbounded Sigma type remains roadmap Stage C; the finite
sum is intentionally honest about the tier-1 value universe and requires no
unsafe cast.

## Runtime architecture

The immutable ordinary-Go `Program` is produced only after parsing and static
checking. A compact tagged VM supports the complete tier-1 universe. When the
AST contains only integers and booleans, compilation selects a machine-word
scalar stack; `RunInt` and `RunBool` are then allocation-free. String presence
selects the general VM. `CompileError` and `RuntimeError` preserve the
compile/evaluate phase distinction at the Go boundary.

The exact language matrix and all intentional semantic differences are in
`expr/COMPATIBILITY.md`; all 617 pinned exported upstream declarations are in
`expr/API_MANIFEST.csv`. Deferred features are never silently interpreted.

## Acceptance evidence

- upstream differential evaluator corpus for the shared tier;
- compile/type rejection corpus and explicit runtime failures;
- existential elaboration and typed evaluator tests;
- executable instruction and cross-package stack-proof tests;
- parser/evaluator fuzzing and race-tested concurrent immutable programs;
- reproducible `.gp` generation, API inventory, tidy module, vet, root tests,
  and standard-library tests;
- five-run typed evaluation measurement of at least 2x upstream speed and at
  least 50% fewer allocations, recorded in `expr/PERFORMANCE.md`.
