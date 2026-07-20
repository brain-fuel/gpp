# G++ (`gpp`)

G++ is a language for authoring richer abstractions while emitting **portable,
idiomatic Go**. It is a **strict superset of Go**: every valid Go file is a
valid G++ file (`.gpp`), and every G++ construct has a specific Go lowering.
Generated packages compile with the standard Go toolchain and may be
distributed and consumed **without** G++ — the same interoperability story
Kotlin, Scala, and Clojure have with Java.

<<<<<<< HEAD
## v0.14.0 — Multi-Pattern Arms

Driven by rune's elaborate/store rewrite — rigidity and spine
classifiers union constructors in one arm:

```go
match t {
case Var(_), Ref(_), Univ(_), Prop:  // one arm, four constructors
	return true
case App(_, _):
	return false
}
```

Alternatives take only wildcard arguments and the arm cannot bind the
value (split the arm to bind); every alternative is its own
reachability row, so a redundant alternative is an unreachable-arm
error and alternatives count toward exhaustiveness.
=======
## v0.13.0 — The Standard Library Grows Nine

Every package extracted from the first whole-system G++ rewrite
([envoy-go](https://github.com/pgdad/envoy-go), ~360k lines): patterns that
appeared three-plus times across an L7 proxy, generalized and shipped where
every G++ program can reach them.

```go
import "goforge.dev/gpp/std/kleene"    // K3 three-valued logic: All/Any short-circuit, Undetermined absorbs
import "goforge.dev/gpp/std/latch"     // one-shot quiescence rendezvous: Inc/Dec/Trip/Done, lock-free hot path
import "goforge.dev/gpp/std/clock"     // time seam + deterministic Fake: (deadline, insertion-seq) Advance ordering
import "goforge.dev/gpp/std/guarded"   // Guarded[T]/RWGuarded[T]: the mutex owns the value, not a comment
import "goforge.dev/gpp/std/deepmap"   // two-level map with defensive Snapshot, nil-receiver tolerant
import "goforge.dev/gpp/std/retry"     // bounded ctx-aware exponential backoff, last-error surfaced
import "goforge.dev/gpp/std/registry"  // freeze-after-boot sealed registry: post-freeze Register panics
import "goforge.dev/gpp/std/memo"      // compute-once cache: compute outside the lock, first-writer-wins identity
import "goforge.dev/gpp/std/closeonce" // idempotent Close with cached first error
```

All nine are authored in G++, tested under -race, and consumed in anger:
envoy-go's drain manager is a latch, its clock package re-exports std/clock,
and its dynamic-metadata bucket embeds a deepmap. No language changes in this
release; the toolchain version moves with std per the one-version discipline.
>>>>>>> origin/main

## v0.11.0 — Deep Structure

The release that arms the rune kernel rewrite: every enum's recursive
structure is now derivable, not hand-rolled.

```go
// Self-recursive enums derive deep traversals (descent sees through
// binder wrappers like Scope{Name string; Body Tm} and slices):
for sub := range TmUniverse(t) { … }        // t + all subterms, preorder
t2 := TmTransform(t, simplify)              // bottom-up rewrite, copies slices

// Monomorphic enums derive structural equality with per-variant hooks —
// proof irrelevance is an override on a derived base, not a hand-written
// walk (handled=false falls through to the derived comparison):
irrelevant := TmEqOverrides{Cast: func(x, y Cast) (bool, bool) {
	return TmEqual(x.A, y.A) && TmEqual(x.B, y.B) && TmEqual(x.X, y.X), true
}}
TmEqualWith(a, b, irrelevant)

// std/option joins std/result: Of/Get at the comma-ok boundary,
// IsSome/IsNone, Map, Bind, UnwrapOr, OrElse.
```

Traversals and equality are nil-tolerant (optional fields like an
elective type annotation pass through untouched), func/map/chan content
makes equality silently underivable (closures have no structure), and
variant doc comments now survive lowering onto the generated structs —
generated Go documents itself on pkg.go.dev.

## v0.10.0 — The Dogfood Rewrite

[goforge.dev/cadence](https://goforge.dev/cadence) v0.2.0 is authored
in G++ — the first external artifact rewritten in the language — and
the rewrite drove three features home:

```go
// Derived rapid generators for every enum (emission is demand-driven —
// law tests, or //gpp:derive gen — so rapid never enters go.mod uninvited):
s := GenStrategy(rt)

// Laws quantify over enums, drawn through the derived generator:
type Interpreter[T any] class {
	Serve(host T, r Region, s Strategy, ctx RequestContext) (Tree, error)
	law Fallback(host T, s Strategy) { … }
}
// → every instance gets a generated rapid property; violations shrink
//   to counterexamples like m={-1}

// Operations declare multiple results; tests are G++ too:
//   foo_test.gpp → foo_gpp_test.go (still a _test.go to the go tool)
```

In cadence, Strategy became a real sum (illegal states unrepresentable),
the hand-rolled FallbackHolds died, and the fallback law is now part of
the Interpreter class — proven automatically for every interpreter
anyone writes.

## v0.9.0 — Tooling: LSP, Editors, go generate

No language changes — this release is about living with gpp:

- **`gpp lsp`** ships inside the binary (one version, always in
  lockstep): diagnostics as you type from the real gen pipeline run in
  memory, plus hover, goto-definition, and completion delegated to
  gopls over the generated Go and mapped back through the sourcemap.
  The server's dispatch layer is authored in gpp itself.
- **Editors**: VS Code (marketplace-ready extension), Neovim, Zed, and
  GoLand/IntelliJ (platform LSP API) — all thin clients of `gpp lsp`;
  see editor/.
- **go generate is canonical**: `gpp init` scaffolds
  `//go:generate go tool gpp gen ./...`; the workflow is
  `go generate ./... && go build ./...`, with the gpp wrapper as
  convenience.
- **Cross-package hardening**: generated files carry a `//gpp:v`
  vintage stamp (a newer file tells you the exact upgrade command);
  marker reconstruction is package-wide; index domains cross packages
  (`Socket[s states.State]`); imported Eq propositions unfold their
  callee's totals; and a missing instance names the transitive package
  that provides one.

## v0.8.0 — Parser Combinators (std/parsec)

```go
import "goforge.dev/gpp/std/parsec"

// A complete arithmetic evaluator: precedence, parens, whitespace.
func grammar() parsec.Parser[int] {
	var expr parsec.Parser[int]
	factor := parsec.Label(parsec.Or(number(), parsec.Between(parsec.Symbol("("), parsec.Defer(&expr), parsec.Symbol(")"))), "expression")
	term := parsec.Chainl1(factor, mulOp())
	expr = parsec.Chainl1(term, addOp())
	return parsec.Then(parsec.Spaces(), parsec.Before(expr, parsec.EOF()))
}

v, err := parsec.RunString(grammar(), "(1+2)*3")   // 9
// errors carry positions and labels:
// 1:3: unexpected '*', expecting expression
```

Parsec-style consumed/empty semantics: `Or` commits once a branch has
consumed input, `Try` restores the lookahead — the discipline that
keeps performance predictable and errors precise. Input STREAMS from
any io.Reader: the buffer retains only what a live `Try` could rewind
to, split UTF-8 runes decode across read boundaries, and a
byte-at-a-time reader parses identically to a string (rapid-tested,
along with the monad identities, Or associativity, and
Try-never-consumes). The library is gpp eating its own cooking: Reply
is a gpp enum matched in every combinator, its derived Fold consumes
replies without a match, and Run's output rides the v0.4 railway.
Also in this release: the linear-value cell is atomic
(`CompareAndSwap`), so even racing double-users get exactly one winner.

## v0.7.0 — The Dependent Core

```go
// Length-indexed vectors: the index is real, checked, and erased.
type Vec[T any, n nat] enum {
	Nil() Vec[T, 0]
	Cons(head T, tail Vec[T, n]) Vec[T, n+1]
}

// 0-quantity parameters exist only at check time:
func Head[T any](0 n nat, v Vec[T, n+1]) T {
	match v {
	case Cons(h, t): // Nil is impossible at n+1 — no other arm needed
		return h
	}
}

// Compiler-verified termination; callable in types:
total func Plus(a, b nat) nat {
	if a == 0 { return b }
	return Plus(a-1, b) + 1
}

// Propositional equality, discharged by the decider:
func Cast[T any](0 n nat, 0 m nat, 0 p Eq[n, m], v Vec[T, n]) Vec[T, m] {
	return v
}
w := Cast(1+1, 2, refl, v) // proves 1+1 = 2; erases to the identity

// Linearity — consumed exactly once, statically AND at runtime:
func Process(1 f *os.File) error { return f.Close() }
```

gpp now carries a real dependent core: quantities (QTT's 0/1/ω plus
multiplicity variables), total functions with structural termination
and guarded nat subtraction, enums indexed by nats, enum tags
(typestate: `Socket[Open]`), and structured first-order data
(`Region[Circle(n), n]`), a normalization-by-evaluation engine where
`n+m ≡ m+n` is definitional, and a sound linear-arithmetic decider
that prunes impossible match arms, discharges `refl` proofs, and
justifies subtraction. Everything erases: indices vanish from the
generated Go, exported dependent functions grow precise runtime guards
for plain-Go callers, and linear values travel as generated use-once
Lin[T] cells that panic on reuse. `std/vec` ships the length-indexed
sequence. Where the decider cannot prove an obligation, the error names
both sides and the workaround — stuck-with-guidance, never silent.

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
algebra.Accumulate(algebra.IntAdd, []int{2, 3, 4})  // 9  — the additive monoid
algebra.Accumulate(algebra.IntMul, []int{2, 3, 4})  // 24 — the multiplicative monoid
```

Explicit witnesses subsume exactly like implicit dispatch (v0.6.1):
`IntAdd` is a `Group` instance, `Accumulate` wants a `Monoid`, and the
compiler inserts the upcast — you name the structure, never the
coercion.

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
# Canonical workflow: the go toolchain drives, gpp only generates.
gpp init                 # scaffold //go:generate wiring (flag: -hook)
go get -tool goforge.dev/gpp/cmd/gpp@latest   # pin gpp in go.mod (Go 1.24+)
go generate ./...        # regenerate *_gpp.go from *.gpp
go build ./...           # plain Go from here (test/vet/run likewise)

# Convenience wrapper: same thing, one word shorter.
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
| v0.7.0  | The dependent core: QTT quantities, total functions, indexed enums, Eq, linearity, std/vec — shipped |
| v0.8.0  | std/parsec: streaming parser combinators — shipped |
| v0.9.0  | Tooling: gpp lsp + four editors, go generate canonical, cross-package hardening — shipped |
| v0.10.0 | The dogfood rewrite: cadence v0.2.0 in G++; derived generators, laws over enums, multi-result ops, G++ tests — shipped |
| v0.11.0 | Deep structure: derived traversals (Children/Universe/Transform), derived structural equality with overrides, std/option, variant doc preservation — shipped |
| v0.13.0 | The standard library grows nine: kleene, latch, clock, guarded, deepmap, retry, registry, memo, closeonce (from the envoy-go rewrite) — shipped |
| v0.14.0 | Multi-pattern match arms — shipped |

## License

MIT — see [LICENSE](LICENSE).
