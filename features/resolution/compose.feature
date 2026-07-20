Feature: Function composition
  f >>> g composes left-to-right into a function value: the first operand
  may take any parameters (one result); each later operand is unary with
  one result. Operands are captured exactly once at composition time.
  Constructor operands infer their type arguments from the incoming type.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Unary chains compose in data-flow order
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      func double(n int) int { return n * 2 }

      func main() {
      	toStr := double >>> double >>> strconv.Itoa
      	fmt.Println(toStr(10) + "!")
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "40!"

  Scenario: The first operand may be n-ary and variadic
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func sum(xs ...int) int {
      	t := 0
      	for _, x := range xs {
      		t += x
      	}
      	return t
      }

      func double(n int) int { return n * 2 }

      func main() {
      	f := sum >>> double
      	fmt.Println(f(1, 2, 3))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "12"

  Scenario: Operands are captured once, at composition time
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      var picks int

      func pick() func(int) int {
      	picks++
      	return func(n int) int { return n + 1 }
      }

      func main() {
      	f := pick() >>> pick()
      	_ = f(0)
      	_ = f(0)
      	fmt.Println("picks:", picks)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "picks: 2"

  Scenario: Partials and composition combine
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func add(a, b int) int { return a + b }
      func mul(a, b int) int { return a * b }

      func main() {
      	f := add(1, _) >>> mul(10, _)
      	fmt.Println(f(3))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "40"

  Scenario: Constructor operands infer from the incoming type
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func (o Option[T]) UnwrapOr(fb T) T {
      	match o {
      	case Some(v):
      		return v
      	case None:
      		return fb
      	}
      }

      func double(n int) int { return n * 2 }

      func main() {
      	toOpt := double >>> Some
      	fmt.Println(toOpt(21).UnwrapOr(0))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "42"

  Scenario: Compositions pipe as segments
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func double(n int) int { return n * 2 }
      func negate(n int) int { return -n }

      func main() {
      	fmt.Println(10 |> double >>> negate)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "-20"

  Scenario: Chain type mismatches are branded errors
    Given a Go+ file "main.gp":
      """
      package main

      import "strconv"

      func double(n int) int { return n * 2 }

      func main() {
      	f := strconv.Itoa >>> double
      	_ = f
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot compose: the previous operand returns string but double takes int"

  Scenario: Non-function and multi-arity operands are branded errors
    Given a Go+ file "main.gp":
      """
      package main

      func add(a, b int) int { return a + b }
      func double(n int) int { return n * 2 }

      func main() {
      	f := double >>> add
      	_ = f
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "a non-first operand of >>> must take exactly one parameter and return one result; add is func(a int, b int) int"
