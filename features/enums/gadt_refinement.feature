Feature: Type-directed GADT refinement
  A refined match arm wraps EVERY mismatched conversion boundary —
  returns, assignments (named results included, so naked returns work),
  call arguments, and the other expected-type contexts — as any(E).(C),
  in both directions (ground→T and T→ground). Only actual mismatches
  wrap: a value flowing through concretely-typed contexts stays bare.
  Function literals bound the walk. The machinery runs one fixpoint
  iteration after the match resolves, via a //goplus:refine carrier that
  never survives into output.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Wraps land at every boundary, and only at mismatches
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Lit(n int) Expr[int]
      	Str(s string) Expr[string]
      	Both(a Expr[T], b Expr[T])
      }

      func show(n int) { fmt.Println("showing", n) }

      func eval[T any](e Expr[T]) T {
      	match e {
      	case Lit(n):
      		v := n + 1
      		show(v)
      		return v
      	case Str(s):
      		return s
      	case Both(a, b):
      		_ = a
      		return eval(b)
      	}
      }

      func main() {
      	fmt.Println(eval(Lit(41)) + 1)
      	fmt.Println(eval(Str("hi")))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      showing 42
      43
      hi
      """
    And the file "main_gp.go" contains:
      """
      		v := n + 1
      		show(v)
      		return any(v).(T)
      """
    And the file "main_gp.go" contains:
      """
      		return any(s).(T)
      """

  Scenario: Sub-position refinement through composite result arguments
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Box[T any] enum {
      	Ints(vs []int) Box[[]int]
      	Anything(v T)
      }

      func first[T any](b Box[[]T]) []T {
      	match b {
      	case Ints(vs):
      		return vs
      	case Anything(v):
      		return v
      	}
      }

      func main() {
      	fmt.Println(first[int](Ints([]int{7, 8})))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[7 8]"
    And the file "main_gp.go" contains:
      """
      		return any(vs).([]T)
      """

  Scenario: Function literals bound the refinement walk
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Lit(n int) Expr[int]
      	Other
      }

      func eval[T any](e Expr[T]) T {
      	match e {
      	case Lit(n):
      		f := func() int { return n }
      		return f()
      	case Other:
      		var zero T
      		return zero
      	}
      }

      func main() {
      	fmt.Println(eval(Lit(5)))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "5"
    And the file "main_gp.go" contains:
      """
      		f := func() int { return n }
      		return any(f()).(T)
      """
