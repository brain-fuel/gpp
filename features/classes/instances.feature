Feature: Instance declarations lower to witness values
  An instance lowers to a package value built by a constructor over a heap
  witness, so member closures see the completed witness (defaults filled
  at resolution, sibling reference allowed). Generic instances lower to
  functions. The //goplus:instance marker makes instances discoverable
  cross-package.

  Scenario: Ground and generic instances
    Given a Go+ file "main.gp":
      """
      package main

      type Monoid[T any] class {
      	Combine(a, b T) T
      	Empty() T
      }

      // IntAdd is addition.
      instance IntAdd Monoid[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      }

      instance SliceConcat[T any] Monoid[[]T] {
      	Combine(a, b []T) []T { return append(append([]T{}, a...), b...) }
      	Empty() []T { return nil }
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 0
    And the file "main_gp.go" contains:
      """
      // IntAdd is addition.
      //
      //goplus:instance IntAdd Monoid[int]
      var IntAdd = func() Monoid[int] {
      	w := &Monoid[int]{
      		Combine: func(a, b int) int { return a + b },
      		Empty:   func() int { return 0 },
      	}
      	return *w
      }()
      """
    And the file "main_gp.go" contains:
      """
      //goplus:instance SliceConcat[T any] Monoid[[]T]
      func SliceConcat[T any]() Monoid[[]T] {
      	w := &Monoid[[]T]{
      		Combine: func(a, b []T) []T { return append(append([]T{}, a...), b...) },
      		Empty:   func() []T { return nil },
      	}
      	return *w
      }
      """

  Scenario: Duplicate implementations are rejected
    Given a Go+ file "main.gp":
      """
      package main

      type M[T any] class {
      	Combine(a, b T) T
      }

      instance X M[int] {
      	Combine(a, b int) int { return a + b }
      	Combine(a, b int) int { return a * b }
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "instance X implements Combine twice"

  Scenario: An instance name collides like any authored name
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """
    And a Go+ file "main.gp":
      """
      package main

      type M[T any] class {
      	Combine(a, b T) T
      }

      type IntAdd struct{}

      instance IntAdd M[int] {
      	Combine(a, b int) int { return a + b }
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "IntAdd"
