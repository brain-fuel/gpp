# G++ (`gpp`)

G++ is a language for authoring richer abstractions while emitting **portable,
idiomatic Go**. It is a **strict superset of Go**: every valid Go file is a
valid G++ file (`.gpp`), and every G++ construct has a specific Go lowering.
Generated packages compile with the standard Go toolchain and may be
distributed and consumed **without** G++ — the same interoperability story
Kotlin, Scala, and Clojure have with Java.

## v0.6.0 — Folds, Full GADTs, Existentials, Delegation

```go
// Structural GADT result types — any type expression per position:
type Expr[T any] enum {
	Wrap(inner Expr[T]) Expr[[]T]
	Flipped(a A, b B) Duo[B, A]      // cross-position
}

// Bounded existentials, erased at the boundary:
type Row[T any] enum {
	Packed[A fmt.Stringer](x A, tag string)
}

// Every enum derives a one-level fold (opt out: //gpp:derive off):
n := Fold(Some(7), OptionCases[int, string]{
	Some: strconv.Itoa,
	None: func() string { return "-" },
})

// Kotlin-style interface delegation:
type Logged struct {
	inner Store delegate   // Logged implements Store; override by declaring
	log   *log.Logger
}
```

GADT result arguments are now arbitrary type expressions, resolved by
structural unification: possibility filtering, case heads, constructor
inference, and refinement all work through composites and cross-position
uses, and refinement wraps EVERY mismatched conversion boundary in an
arm (naked returns included) — only actual mismatches wrap. Where Go's
erasure cannot name a case head (a composite argument matched at a bare
type parameter), the arm is a guided error and `case _:` covers it.
Existential type variables must carry an interface bound — Go cannot
express a match arm generic in a hidden type — and erase to that bound
in fields, constructors, and binders. `std/result` now ships a derived
`result.Fold(r, result.ResultCases[T, E, R]{Ok: …, Err: …})`.

## v0.5.0 — Typeclasses

Lean-flavored classes, named instances, implicit dispatch, and a
law-tested algebraic hierarchy — all lowering to plain Go witness
structs a Go consumer can call directly:

```go
type Monoid[T any] class {
	Semigroup[T]
	Empty() T
	law LeftId(a T) { return reflect.DeepEqual(Combine(Empty(), a), a) }
}

instance IntAdd Group[int] {
	Combine(a, b int) int { return a + b }
	Empty() int { return 0 }
	Invert(a int) int { return -a }
}

func Accumulate[T Monoid](xs []T) T {
	acc := Empty()
	for _, x := range xs {
		acc = Combine(acc, x)
	}
	return acc
}

Accumulate([]int{1, 2, 3})   // one Monoid[int] instance in scope: found implicitly
```

A class is an algebraic structure in the mathematical sense: a carrier
set (the instantiating type) together with operations on it, satisfying
declared laws — a `Monoid` is the triple (T, `Combine`, `Empty`) with
associativity and a two-sided identity, and an instance names one
concrete such structure. That is why int has TWO monoids, and why
implicit resolution refuses to pick between them: with `std/algebra`
imported, `Accumulate([]int{…})` is ambiguous between `IntAdd` (a Group,
by subsumption) and `IntMul`, and the error names both. You disambiguate
by naming the structure you mean:

```go
algebra.Accumulate(algebra.IntAdd.AsMonoid(), []int{2, 3, 4})  // 9  — the additive monoid
algebra.Accumulate(algebra.IntMul, []int{2, 3, 4})             // 24 — the multiplicative monoid
```

A class lowers to a flat witness struct (`Monoid[T]` with `func` fields);
an instance to a package value; a class constraint to a leading witness
parameter that call sites receive implicitly. Classes embed to form
hierarchies (diamonds collapse; upcasts are generated), operations may
carry **default bodies** instances can omit, and a **stronger instance
satisfies a weaker constraint** (a `Group[int]` instance answers a
`[T Monoid]` call). Ambiguity is a hard error naming the candidates; the
escape hatch is calling the lowered signature directly. `law` members
declare boolean properties over the operations, and **law tests generate
by default** for every concrete instance (rapid properties, inherited
laws included) with `//gpp:laws` knobs (`off`, `[int] [string]`
instantiations for generic instances, `gen=`, package-level `out=`).
`goforge.dev/gpp/std/algebra` ships the Magma→Group hierarchy, stock
instances, and `Accumulate`/`FoldMap`.

## v0.4.0 — Typed Failure

Railway-Oriented error handling in the Wlaschin style: a shipped
`Result[T, E]` library, track-aware pipelines, Kleisli composition,
postfix `?` propagation, and expression-oriented control flow.

```go
import "goforge.dev/gpp/std/result"

// Track-aware |>: once a Result flows, stages lift by shape —
// T→Result binds, T→(U, error) adapts, T→U maps, T→() tees (Ok only),
// dot segments see the raw Result. Err bypasses everything.
n := s |> validate |> strings.TrimSpace |> strconv.Atoi |> audit |> .UnwrapOr(0)

// Kleisli >=>: compose fallible steps; plain steps lift, the rail
// opens at the first step that can fail, Err short-circuits.
pipeline := strings.TrimSpace >=> validate >=> strconv.Atoi >=> save
// (value, error) functions adapt automatically: strconv.Atoi >=> double

// Postfix ?: propagate failure to the enclosing function.
data := os.ReadFile(path)?          // (…, error) enclosing: zero-value early return
n := parse(s)?                      // Result enclosing: returns Err, typed errors preserved

// Expression-oriented if / switch / match — arms are single expressions.
y := if x > 2 { "big" } else { "small" }
grade := switch score {
case 10:
	"A"
default:
	"B"
}
area := match shape {
case Circle(r):
	3.14 * r * r
case Rect(w, h):
	w * h
}
```

`goforge.dev/gpp/std` is a nested module with **zero dependencies**,
written in G++ and shipped as generated Go (`go get goforge.dev/gpp/std`).
`Result[T any, E error]` carries typed failures; `Of` enters the railway
from a Go-shaped `(value, error)` pair, `Unpack` leaves it. `?` works with
Result values, `(…, error)` calls, and bare errors, in both Go-shaped and
Result-shaped functions. Expression forms hoist to statements before their
anchor — hoisted sites evaluate before the rest of their statement, in
source order — and a match expression gets the full v0.2.0 machinery:
exhaustiveness, GADT refinement, nested patterns.

## v0.3.0 — Functional Flow

Pipelines, composition, partial application, and placeholders — all
lowering to the plain Go you would have written:

```go
total := xs |> Filter(isEven) |> Map(double) |> Sum
// Sum(StackMap(StackFilter(xs, isEven), double))

answer := 21 |> Some |> .Map(double).UnwrapOr(0)

toStr  := double >>> strconv.Itoa      // func(int) string
inc    := add(1, _)                    // partial application
between:= clamp(_, lo, hi)             // placeholder anywhere in a call
```

`x |> f(a)` inserts the piped value as the first argument (a placeholder
`_` picks a different slot); bare-name segments are **method-aware**: they
resolve against the piped value's members — full Go selector semantics
plus G++ generic and enum methods — and against functions, constructors,
builtins, and conversions in scope. Resolving to *both* is a hard error
naming the two explicit spellings (`.Map(f)` for the member, `Map(_, f)`
for the function). Multi-result stages follow Go's spread rule
(`"42" |> strconv.Atoi |> handle` when `handle(int, error)`). `>>>`
composes left-to-right into a capture-once closure, constructor operands
included (`double >>> Some`). Partials capture their callee and fixed
arguments exactly once at creation, method receivers bind-time.

## v0.2.0 — Algebraic Data Types

Sum types with exhaustive pattern matching, constructor generation, and
initial GADT support — lowered to sealed interfaces plus variant structs
that plain Go consumes with an ordinary type switch:

```go
// option.gpp
package option

type Option[T any] enum {
	Some(value T)
	None
}

func (o Option[T]) Map[U any](f func(T) U) Option[U] {
	match o {
	case Some(v):
		return Some(f(v))
	case None:
		return None
	}
}
```

`match` is exhaustive: a missing variant is a compile error with a witness
(`non-exhaustive match on Shape: missing Rect(_, _)`), checked by Maranget
usefulness so nested patterns like `Add(Lit(a), Lit(b))` are covered
correctly. Constructors infer their type arguments from arguments or the
expected type (`var o Option[int] = None`), auto-wrap into closures in
function position (`xs.Map(Some)`), and qualify (`Option[int].None`) when a
name is genuinely ambiguous. GADT variants may pin their result type —
`Lit(v int) Expr[int]` — excluding impossible arms and refining type
parameters inside matching arms (the classic typed interpreter works).
Emitted enums carry `//gpp:enum`/`//gpp:variant` markers, so importing
packages get constructors, matching, and exhaustiveness from the committed
Go artifact alone.

```go
// emitted
type Option[T any] interface{ isOption(T) }

type Some[T any] struct{ Value T }
func (Some[T]) isOption(T) {}
// … plain-Go consumer:
switch v := o.(type) {
case option.Some[int]:
	fmt.Println(v.Value)
}
```

## v0.1.0 — Generic Methods

Methods may introduce type parameters not present on their receivers:

```go
// stack.gpp
package stack

type Stack[T any] struct{ items []T }

func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
    out := Stack[U]{items: make([]U, 0, len(s.items))}
    for _, x := range s.items {
        out.items = append(out.items, f(x))
    }
    return out
}
```

`gpp gen` emits `stack_gpp.go` beside the source — committed to your repo,
protobuf-style — lowering each generic method to a package-level generic
function:

```go
// Code generated by gpp from stack.gpp. DO NOT EDIT.

//gpp:method (Stack[T]) Map[U]
func StackMap[T any, U any](s Stack[T], f func(T) U) Stack[U] { … }
```

G++ callers keep method syntax — `s.Map(strconv.Itoa)` — including chained
calls, explicit instantiation (`s.Map[string](f)`), method values
(`f := s.Map[string]`), and promotion through embedded fields. Plain-Go
consumers of your published package call `stack.StackMap(s, strconv.Itoa)`.
The `//gpp:method` marker makes the emitted file self-describing, so packages
that import yours get method syntax too — even when your package is fetched
as ordinary Go with `go get`.

## CLI

```
gpp gen ./...            # generate *_gpp.go from *.gpp
gpp gen -check ./...     # exit 1 if any generated file is stale (CI)
gpp gen -stage ./...     # regenerate and git-add results (pre-commit)
gpp build|test|run|vet   # generate, then delegate to the go tool
gpp version
```

## Install

```
go install goforge.dev/gpp/cmd/gpp@latest
```

The standard library is a separate, dependency-free module:

```
go get goforge.dev/gpp/std@latest
```

## Keeping generated code fresh

Use the [pre-commit](https://pre-commit.com) framework:

```yaml
# .pre-commit-config.yaml
repos:
  - repo: https://github.com/brain-fuel/gpp
    rev: v0.1.0
    hooks:
      - id: gpp-gen
```

When outputs are stale, the first `git commit` attempt regenerates **and
stages** the fixed files, then aborts (pre-commit's behavior for any hook that
modifies files); retry the commit and it passes. `gpp-check` is a
verify-only variant for CI.

## Specification

The spec is executable: the Godog/Cucumber feature suite under
[`features/`](features/) plus the grammar deltas in
[`spec/`](spec/) (one EBNF per milestone). Run it with `go test ./...`.

## Limitations (by design)

- A lowered generic method is a function, not a method — it cannot help a
  type satisfy an interface. This is fundamental to the lowering (Go
  interfaces cannot express generic methods) and will not change.
- Uninstantiated generic method values (`f := s.Map`) are errors, matching
  Go's rule for uninstantiated generic function values.
- Match subjects may not start with `(`, `[`, `{`, or `<-` (those spellings
  stay valid Go); bind such subjects to a variable first. Literal patterns
  and guards arrive in a later milestone.
- v0.2.0 GADT result-type arguments are the enum's own type parameter or a
  ground named type per position; refinement applies to `T`-typed returns
  (use `any(x).(T)` manually elsewhere).
- `|>` and `>>>` are the lowest-precedence operators; `xs |> len > 0`
  parses as `xs |> (len > 0)` and gets a parenthesize hint. Placeholders
  cannot stand for variadic parameters, and `_.Method` receivers wait for
  a later milestone.
- `?` and expression if/switch/match lower by hoisting statements, so they
  cannot appear where an early return or eager evaluation would change
  semantics: for conditions/post statements, else-if conditions, the right
  side of `&&`/`||`, case values, select communications, assignment
  left-hand sides, whole deferred/go calls, or package level (each is a
  guided error).

## Roadmap

| Version | Theme |
| ------- | ----- |
| v0.1.0  | Generic methods — shipped |
| v0.2.0  | Algebraic data types, exhaustive matching — shipped |
| v0.3.0  | Pipelines, composition, partial application — shipped |
| v0.4.0  | Typed failure: std/result, railway pipes, Kleisli `>=>`, postfix `?`, expression-oriented control flow — shipped |
| v0.5.0  | Typeclasses: classes, instances, implicit dispatch, laws, std/algebra — shipped |
| v0.6.0  | Folds, structural GADTs, bounded existentials, delegation — shipped |
| v0.7.0  | std/parsec: parser combinators |

## License

MIT — see [LICENSE](LICENSE).
