Feature: Lowering enum declarations
  An enum lowers to a sealed interface (unexported marker method whose
  parameters are the enum's type parameters — tying every variant instance
  to exactly one interface instance) plus one struct per variant.
  //gpp:enum and //gpp:variant markers make the emitted Go self-describing.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Option lowers to a sealed generic interface with variant structs
    Given a G++ file "option.gpp":
      """
      package demo

      // Option is an optional value.
      type Option[T any] enum {
      	Some(value T)
      	None
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 0
    And the file "option_gpp.go" contains:
      """
      // Option is an optional value.
      //
      //gpp:enum Option[T any]
      type Option[T any] interface{ isOption(T) }
      """
    And the file "option_gpp.go" contains:
      """
      //gpp:variant (Option[T]) Some(value T)
      type Some[T any] struct {
      	Value T
      }

      func (Some[T]) isOption(T) {}
      """
    And the file "option_gpp.go" contains:
      """
      //gpp:variant (Option[T]) None
      type None[T any] struct{}

      func (None[T]) isOption(T) {}
      """
    And running gpp with arguments "gen -check ." exits with 0
    And running gpp with arguments "vet ./..." exits with 0

  Scenario: Result carries every enum type parameter on every variant
    Given a G++ file "result.gpp":
      """
      package demo

      type Result[T any, E any] enum {
      	Ok(value T)
      	Err(err E)
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 0
    And the file "result_gpp.go" contains:
      """
      type Result[T any, E any] interface{ isResult(T, E) }
      """
    And the file "result_gpp.go" contains:
      """
      //gpp:variant (Result[T, E]) Ok(value T)
      type Ok[T any, E any] struct {
      	Value T
      }

      func (Ok[T, E]) isResult(T, E) {}
      """

  Scenario: GADT variants pin the interface instance they implement
    Given a G++ file "expr.gpp":
      """
      package demo

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	Bl(b bool) Expr[bool]
      	Add(l, r Expr[int]) Expr[int]
      	If(c Expr[bool], t, e Expr[T])
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 0
    And the file "expr_gpp.go" contains:
      """
      //gpp:variant (Expr[T]) Lit(v int) Expr[int]
      type Lit struct {
      	V int
      }

      func (Lit) isExpr(int) {}
      """
    And the file "expr_gpp.go" contains:
      """
      //gpp:variant (Expr[T]) If(c Expr[bool], t, e Expr[T])
      type If[T any] struct {
      	C Expr[bool]
      	T Expr[T]
      	E Expr[T]
      }

      func (If[T]) isExpr(T) {}
      """

  Scenario: GADT field types follow their fixed type parameters
    Given a G++ file "boxed.gpp":
      """
      package demo

      type Boxed[T any] enum {
      	Ints(xs []T, mk func() T) Boxed[int]
      	Free(v T)
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 0
    And the file "boxed_gpp.go" contains:
      """
      type Ints struct {
      	Xs []int
      	Mk func() int
      }

      func (Ints) isBoxed(int) {}
      """

  Scenario: Visibility follows the enum and variant names
    Given a G++ file "vis.gpp":
      """
      package demo

      type route enum {
      	Local(path string)
      	remote(host string)
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 0
    And the file "vis_gpp.go" contains:
      """
      type route interface{ isRoute() }
      """
    And the file "vis_gpp.go" contains:
      """
      type local struct {
      	path string
      }
      """
    And the file "vis_gpp.go" contains:
      """
      type remote struct {
      	host string
      }
      """

  Scenario: A variant name shared by two enums prefixes both lowered structs
    Given a G++ file "shared.gpp":
      """
      package demo

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      type List[T any] enum {
      	Cons(head T, tail List[T])
      	None
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 0
    And the file "shared_gpp.go" contains:
      """
      //gpp:variant (Option[T]) None
      type OptionNone[T any] struct{}
      """
    And the file "shared_gpp.go" contains:
      """
      //gpp:variant (List[T]) None
      type ListNone[T any] struct{}
      """
    And the file "shared_gpp.go" contains:
      """
      type Some[T any] struct {
      """

  Scenario: //gpp:name overrides a variant's lowered struct name
    Given a G++ file "named.gpp":
      """
      package demo

      type List[T any] enum {
      	Cons(head T, tail List[T])
      	//gpp:name Nil
      	None
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 0
    And the file "named_gpp.go" contains:
      """
      //gpp:variant (List[T]) None
      type Nil[T any] struct{}
      """

  Scenario: A variant colliding with an authored declaration is an error
    Given a file "clash.go":
      """
      package demo

      type Circle struct{ R float64 }
      """
    And a G++ file "shape.gpp":
      """
      package demo

      type Shape enum {
      	Circle(r float64)
      	Point
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "generated name Circle"
    And stderr contains "//gpp:name"

  Scenario: A zero-variant enum is rejected
    Given a G++ file "empty.gpp":
      """
      package demo

      type Nothing enum {
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "enum Nothing must declare at least one variant"

  Scenario: An unsupported GADT result type is rejected
    Given a G++ file "bad.gpp":
      """
      package demo

      type Expr[T any] enum {
      	Sliced(v int) Expr[[]T]
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "unsupported result type"

  Scenario: Enum generation is deterministic and idempotent
    Given a G++ file "option.gpp":
      """
      package demo

      type Option[T any] enum {
      	Some(value T)
      	None
      }
      """
    When I run gpp with arguments "gen ."
    And I record the generated files
    And I run gpp with arguments "gen ."
    Then the generated files are unchanged
    And running gpp with arguments "gen -check ." exits with 0
