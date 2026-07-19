Feature: Indexed enums (nat indices)
  An enum type parameter constrained by `nat` is a VALUE INDEX: it
  exists only at check time. Variant results and fields may instantiate
  the enum at index TERMS (`Vec[T, 0]`, `Vec[T, n+1]`); erasure drops
  index binders from the generated type parameters and index arguments
  from every instantiation — ordinary code writes the indexed form and
  the generated Go never sees it. The unerased declaration travels in
  the //gpp:enum and //gpp:variant markers, so indexed enums cross
  packages like any other. Index checking at ordinary boundaries is the
  dependent-signature layer (a later phase); erasure alone is exact.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Declaration, construction, match, and fold erase and run
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Vec[T any, n nat] enum {
      	Nil() Vec[T, 0]
      	Cons(head T, tail Vec[T, n]) Vec[T, n+1]
      }

      func sum(v Vec[int, 2]) int {
      	total := 0
      	match v {
      	case Nil():
      		total = -1
      	case Cons(h, t):
      		total = h
      		match t {
      		case Nil():
      		case Cons(h2, t2):
      			total += h2
      			_ = t2
      		}
      	}
      	return total
      }

      func main() {
      	var v Vec[int, 2] = Cons(1, Cons(2, Nil[int]()))
      	fmt.Println(sum(v))
      	fmt.Println(Fold(v, VecCases[int, string]{
      		Nil:  func() string { return "-" },
      		Cons: func(h int, t Vec[int]) string { return fmt.Sprint(h) },
      	}))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      3
      1
      """
    And the file "main_gpp.go" contains:
      """
      //gpp:enum Vec[T any, n nat]
      type Vec[T any] interface{ isVec(T) }
      """
    And the file "main_gpp.go" contains:
      """
      //gpp:variant (Vec[T]) Cons(head T, tail Vec[T, n]) Vec[T, n+1]
      type Cons[T any] struct {
      """
    And the file "main_gpp.go" contains:
      """
      func sum(v Vec[int]) int {
      """

  Scenario: An index-only enum erases to a plain type
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Counter[n nat] enum {
      	Start() Counter[0]
      	Tick(prev Counter[n]) Counter[n+1]
      }

      func depth(c Counter[2]) int {
      	match c {
      	case Start():
      		return 0
      	case Tick(p):
      		return depthAny(p) + 1
      	}
      	return -1
      }

      func depthAny(c Counter[1]) int {
      	match c {
      	case Start():
      		return 0
      	case Tick(p):
      		_ = p
      		return 1
      	}
      	return -1
      }

      func main() {
      	fmt.Println(depth(Tick(Tick(Start()))))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "2"
    And the file "main_gpp.go" contains:
      """
      type Counter interface{ isCounter() }
      """
    And the file "main_gpp.go" contains:
      """
      func depth(c Counter) int {
      """

  Scenario: Indexed enums cross packages through their markers
    Given a G++ file "vec/vec.gpp":
      """
      package vec

      type Vec[T any, n nat] enum {
      	Nil() Vec[T, 0]
      	Cons(Head T, Tail Vec[T, n]) Vec[T, n+1]
      }
      """
    And a G++ file "main.gpp":
      """
      package main

      import (
      	"fmt"

      	"example.com/demo/vec"
      )

      func sum(v vec.Vec[int, 2]) int {
      	total := 0
      	match v {
      	case vec.Nil():
      		total = -1
      	case vec.Cons(h, t):
      		total = h
      		_ = t
      	}
      	return total
      }

      func main() {
      	var v vec.Vec[int, 2] = vec.Cons(10, vec.Cons(2, vec.Nil[int]()))
      	fmt.Println(sum(v))
      }
      """
    When I run gpp with arguments "gen ./..."
    Then the exit code is 0
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "10"
    And the file "main_gpp.go" contains:
      """
      func sum(v vec.Vec[int]) int {
      """

  Scenario: An index parameter cannot be used as a type
    Given a G++ file "main.gpp":
      """
      package main

      type V[T any, n nat] enum {
      	A(x T) V[n, 0]
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "variant A: index parameter n cannot be used as a type"

  Scenario: A type parameter cannot be used as an index
    Given a G++ file "main.gpp":
      """
      package main

      type V[T any, n nat] enum {
      	A(x T) V[T, T]
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "index argument T uses T, which is not an index parameter of the enum"

  Scenario: Index arguments may only use the enum's index binders
    Given a G++ file "main.gpp":
      """
      package main

      type V[T any, n nat] enum {
      	A(x V[T, m]) V[T, n]
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "index argument m uses m, which is not an index parameter of the enum"
