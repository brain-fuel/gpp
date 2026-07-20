Feature: Parsing enum declarations
  Go+ v0.2.0 adds sum types via a contextual `enum` keyword after a type
  name (spec/grammar-v0.2.0.ebnf). Variants carry constructor parameters,
  and an optional GADT result type.

  Scenario: A plain enum with parameterized and bare variants
    Given a Go+ file "shape.gp":
      """
      package shape

      type Shape enum {
      	// Circle is round.
      	Circle(r float64)
      	Rect(w, h float64)
      	Point
      }
      """
    When I parse it
    Then parsing succeeds with 1 enum
    And enum 1 is "Shape: Circle(r float64) | Rect(w, h float64) | Point"

  Scenario: A generic enum
    Given a Go+ file "option.gp":
      """
      package option

      type Option[T any] enum {
      	Some(value T)
      	None
      }
      """
    When I parse it
    Then parsing succeeds with 1 enum
    And enum 1 is "Option[T]: Some(value T) | None"

  Scenario: GADT variants declare result types
    Given a Go+ file "expr.gp":
      """
      package expr

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	Bl(b bool) Expr[bool]
      	If(c Expr[bool], t, e Expr[T])
      }
      """
    When I parse it
    Then parsing succeeds with 1 enum
    And enum 1 variant "Lit" has result type "Expr[int]"
    And enum 1 variant "Bl" has result type "Expr[bool]"
    And enum 1 variant "If" has result type ""

  Scenario: Nullary variants may be written with or without parentheses
    Given a Go+ file "u.gp":
      """
      package u

      type Unit enum {
      	U()
      	V
      }
      """
    When I parse it
    Then parsing succeeds with 1 enum
    And enum 1 is "Unit: U() | V"

  Scenario: Enums coexist with generic methods in one file
    Given a Go+ file "both.gp":
      """
      package both

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	return Stack[U]{}
      }
      """
    When I parse it
    Then parsing succeeds with 1 enum
    And parsing succeeds with 1 generic method

  Scenario: Unnamed variant fields are rejected
    Given a Go+ file "bad.gp":
      """
      package bad

      type Shape enum {
      	Circle(float64)
      }
      """
    When I parse it
    Then parsing fails with an error containing "enum variant fields must be named"

  Scenario: Variadic variant fields are rejected
    Given a Go+ file "bad.gp":
      """
      package bad

      type Bag enum {
      	Of(xs ...int)
      }
      """
    When I parse it
    Then parsing fails with an error containing "enum variant fields cannot be variadic"

  Scenario: Enum aliases are rejected
    Given a Go+ file "bad.gp":
      """
      package bad

      type Shape = enum {
      	Point
      }
      """
    When I parse it
    Then parsing fails with an error containing "enum declarations cannot be type aliases"
