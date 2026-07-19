Feature: Dependent signatures
  A function whose parameters carry quantities or mention nat is
  DEPENDENT: nat erases to int, 0-quantity parameters vanish from the
  erased signature AND their arguments vanish from every call site (the
  surface stays fully applied — `Head(2, v)` — and erasure drops both
  ends), and the original signature travels in a //gpp:dep marker.
  Erased arguments must be pure index expressions: their evaluation
  does not survive erasure.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Head and Replicate erase and run
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Vec[T any, n nat] enum {
      	Nil() Vec[T, 0]
      	Cons(head T, tail Vec[T, n]) Vec[T, n+1]
      }

      func Head[T any](0 n nat, v Vec[T, n+1]) T {
      	match v {
      	case Cons(h, t):
      		_ = t
      		return h
      	case _:
      		panic("unreachable")
      	}
      }

      func Replicate[T any](n nat, x T) Vec[T, n] {
      	if n == 0 {
      		return Nil[T]()
      	}
      	return Cons(x, Replicate(n-1, x))
      }

      func main() {
      	v := Replicate(3, "a")
      	fmt.Println(Head(2, v))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "a"
    And the file "main_gpp.go" contains:
      """
      //gpp:dep Head[T any](0 n nat, v Vec[T, n+1]) T
      func Head[T any](v Vec[T]) T {
      """
    And the file "main_gpp.go" contains:
      """
      //gpp:dep Replicate[T any](n nat, x T) Vec[T, n]
      func Replicate[T any](n int, x T) Vec[T] {
      """
    And the file "main_gpp.go" contains:
      """
      	fmt.Println(Head(v))
      """

  Scenario: Dependent functions cross packages through their markers
    Given a G++ file "vec/vec.gpp":
      """
      package vec

      type Vec[T any, n nat] enum {
      	Nil() Vec[T, 0]
      	Cons(Head T, Tail Vec[T, n]) Vec[T, n+1]
      }

      func First[T any](0 n nat, v Vec[T, n+1]) T {
      	match v {
      	case Cons(h, t):
      		_ = t
      		return h
      	case _:
      		panic("unreachable")
      	}
      }
      """
    And a G++ file "main.gpp":
      """
      package main

      import (
      	"fmt"

      	"example.com/demo/vec"
      )

      func main() {
      	v := vec.Cons(7, vec.Nil[int]())
      	fmt.Println(vec.First(0, v))
      }
      """
    When I run gpp with arguments "gen ./..."
    Then the exit code is 0
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "7"
    And the file "main_gpp.go" contains:
      """
      	fmt.Println(vec.First(v))
      """

  Scenario: An effectful erased argument is rejected
    Given a G++ file "main.gpp":
      """
      package main

      type Vec[T any, n nat] enum {
      	Nil() Vec[T, 0]
      	Cons(head T, tail Vec[T, n]) Vec[T, n+1]
      }

      func Head[T any](0 n nat, v Vec[T, n+1]) T {
      	match v {
      	case Cons(h, t):
      		_ = t
      		return h
      	case _:
      		panic("unreachable")
      	}
      }

      func sideEffect() int {
      	return 1
      }

      func main() {
      	v := Cons("x", Nil[string]())
      	ch := make(chan int, 1)
      	_ = Head(<-ch, v)
      	_ = sideEffect
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "the argument for erased parameter n of Head must be an index expression (it is erased at runtime)"
