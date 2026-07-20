Feature: Dependent signatures
  A function whose parameters carry quantities or mention nat is
  DEPENDENT: nat erases to int, 0-quantity parameters vanish from the
  erased signature AND their arguments vanish from every call site (the
  surface stays fully applied — `Head(2, v)` — and erasure drops both
  ends), and the original signature travels in a //goplus:dep marker.
  Erased arguments must be pure index expressions: their evaluation
  does not survive erasure.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Head and Replicate erase and run
    Given a Go+ file "main.gp":
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
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "a"
    And the file "main_gp.go" contains:
      """
      //goplus:dep Head[T any](0 n nat, v Vec[T, n+1]) T
      func Head[T any](v Vec[T]) T {
      """
    And the file "main_gp.go" contains:
      """
      //goplus:dep Replicate[T any](n nat, x T) Vec[T, n]
      func Replicate[T any](n int, x T) Vec[T] {
      """
    And the file "main_gp.go" contains:
      """
      	fmt.Println(Head(v))
      """

  Scenario: Dependent functions cross packages through their markers
    Given a Go+ file "vec/vec.gp":
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
      	}
      }
      """
    And a Go+ file "main.gp":
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
    When I run goplus with arguments "gen ./..."
    Then the exit code is 0
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "7"
    And the file "main_gp.go" contains:
      """
      	fmt.Println(vec.First(v))
      """

  Scenario: An effectful erased argument is rejected
    Given a Go+ file "main.gp":
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
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "the argument for erased parameter n of Head must be an index expression (it is erased at runtime)"

  Scenario: Exported dependent functions guard their erased preconditions
    Given a Go+ file "main.gp":
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
      	}
      }

      func main() {
      	fmt.Println(Head(0, Cons(9, Nil[int]())))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "9"
    And the file "main_gp.go" contains:
      """
      	if _, ok := any(v).(Nil[T]); ok {
      		panic("goplus: Head: v with index n+1 cannot be Nil")
      	}
      """

  Scenario: The guard fires when plain Go passes an impossible value
    Given a Go+ file "lib/lib.gp":
      """
      package lib

      type Vec[T any, n nat] enum {
      	Nil() Vec[T, 0]
      	Cons(head T, tail Vec[T, n]) Vec[T, n+1]
      }

      func Head[T any](0 n nat, v Vec[T, n+1]) T {
      	match v {
      	case Cons(h, t):
      		_ = t
      		return h
      	}
      }
      """
    And a file "main.go":
      """
      package main

      import (
      	"fmt"

      	"example.com/demo/lib"
      )

      func main() {
      	defer func() {
      		fmt.Println("recovered:", recover())
      	}()
      	fmt.Println(lib.Head[int](lib.Nil[int]{}))
      }
      """
    When I run goplus with arguments "gen ./..."
    Then the exit code is 0
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "recovered: goplus: Head: v with index n+1 cannot be Nil"

  Scenario: The scrutinee's index makes impossible arms an error and wildcards unnecessary
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Vec[T any, n nat] enum {
      	Nil() Vec[T, 0]
      	Cons(head T, tail Vec[T, n]) Vec[T, n+1]
      }

      func Head[T any](0 n nat, v Vec[T, n+1]) T {
      	match v {
      	case Nil():
      		panic("empty")
      	case Cons(h, t):
      		_ = t
      		return h
      	}
      }

      func main() {
      	fmt.Println(Head(0, Cons(1, Nil[int]())))
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "pattern Nil() can never match: the scrutinee's index (n+1) rules out Nil (its index is 0)"
