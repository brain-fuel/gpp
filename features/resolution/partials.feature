Feature: Partial application
  A call with top-level `_` arguments is a closure with one parameter per
  placeholder, in argument order. The callee (when it is a value — method
  values included) and every fixed argument are captured exactly once at
  creation time.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Plain and multi-fixed partials
    Given a G++ file "main.gpp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      func add(a, b int) int { return a + b }

      func main() {
      	inc := add(1, _)
      	parse := strconv.ParseInt(_, 10, 64)
      	n, _ := parse("42")
      	fmt.Println(inc(41), n)
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "42 42"

  Scenario: Multiple placeholders become parameters in order
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      func between(lo, n, hi int) bool { return lo <= n && n <= hi }

      func main() {
      	f := between(_, 5, _)
      	fmt.Println(f(1, 10), f(6, 10))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "true false"

  Scenario: Generic callees infer type arguments from fixed arguments
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      func mapSlice[A any, B any](xs []A, f func(A) B) []B {
      	out := make([]B, 0, len(xs))
      	for _, x := range xs {
      		out = append(out, f(x))
      	}
      	return out
      }

      func double(n int) int { return n * 2 }

      func main() {
      	onInts := mapSlice(_, double)
      	fmt.Println(onInts([]int{1, 2, 3}))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "[2 4 6]"
    And the file "main_gpp.go" contains:
      """
      mapSlice[int, int](__gpp_p0, __gpp_c0)
      """

  Scenario: Uninferable generic partials demand instantiation
    Given a G++ file "main.gpp":
      """
      package main

      func pick[T any](xs []T, i int) T { return xs[i] }

      func main() {
      	f := pick(_, 0)
      	_ = f
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot infer the type arguments of pick from its non-placeholder arguments; instantiate it"

  Scenario: Method partials capture the receiver at bind time
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Counter struct{ n int }

      func (c Counter) AddTo(x int) int { return c.n + x }

      func main() {
      	c := Counter{n: 10}
      	f := c.AddTo(_)
      	c.n = 99
      	fmt.Println(f(5))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "15"

  Scenario: Fixed arguments evaluate exactly once, at creation
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      var evals int

      func fixed() int {
      	evals++
      	return 100
      }

      func add(a, b int) int { return a + b }

      func main() {
      	f := add(fixed(), _)
      	_ = f(1)
      	_ = f(2)
      	fmt.Println("evals:", evals)
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "evals: 1"

  Scenario: Constructor partials produce enum-typed closures
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type List[T any] enum {
      	Cons(head T, tail List[T])
      	Nil
      }

      func length[T any](l List[T]) int {
      	match l {
      	case Cons(_, rest):
      		return 1 + length(rest)
      	case Nil:
      		return 0
      	}
      }

      func main() {
      	var nl List[int] = Nil
      	push := Cons(_, Cons(2, nl))
      	fmt.Println(length(push(1)))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "2"

  Scenario: Placeholders cannot stand for variadic parameters
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      func main() {
      	f := fmt.Sprintln(_)
      	_ = f
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "_ cannot stand for a variadic parameter in v0.3.0"

  Scenario: Partials compose with pipelines
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      func mul(a, b int) int { return a * b }

      func addAll(base int, xs []int) int {
      	for _, x := range xs {
      		base += x
      	}
      	return base
      }

      func apply(n int, f func(int) int) int { return f(n) }

      func main() {
      	fmt.Println(7 |> apply(mul(6, _)) |> addAll([]int{1, 2}))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "45"
