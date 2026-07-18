Feature: Class operations as bare names, receiver sugar, and pipes
  Inside constrained functions, law and default bodies, and instance
  constructors, class operations are in scope as bare names. A bare name
  that also resolves in ordinary scope is a hard error demanding
  qualification through the deterministic witness parameter name.
  Receiver sugar a.Combine(b) and pipe segments xs |> Op apply when the
  receiver or flowing type is a constrained type parameter.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: A bare op colliding with a package name demands qualification
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Monoid[T any] class {
      	Combine(a, b T) T
      	Empty() T
      }

      func Combine(a, b string) string { return a + b }

      func Accumulate[T Monoid](xs []T) T {
      	acc := Empty()
      	for _, x := range xs {
      		acc = Combine(acc, x)
      	}
      	return acc
      }

      func main() {
      	fmt.Println(Combine("a", "b"))
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "Combine is both an operation of Monoid and a name in scope; write monoid.Combine for the operation or qualify the other use"

  Scenario: Qualifying through the witness parameter resolves the collision
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Monoid[T any] class {
      	Combine(a, b T) T
      	Empty() T
      }

      instance IntAdd Monoid[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      }

      func Combine(a, b string) string { return a + b }

      func Accumulate[T Monoid](xs []T) T {
      	acc := Empty()
      	for _, x := range xs {
      		acc = monoid.Combine(acc, x)
      	}
      	return acc
      }

      func main() {
      	fmt.Println(Accumulate([]int{2, 3}), Combine("a", "b"))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "5 ab"

  Scenario: Instance members reference siblings and inherited defaults
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Countdown[T any] class {
      	Step(a T) T
      	Twice(a T) T { return Step(Step(a)) }
      }

      instance IntStep Countdown[int] {
      	Step(a int) int { return a - 1 }
      }

      func main() {
      	fmt.Println(IntStep.Step(10), IntStep.Twice(10))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "9 8"
