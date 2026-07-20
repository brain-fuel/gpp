Feature: Kleisli composition with >=>
  `>=>` composes on the railway: the chain folds left-to-right with track
  state. The rail opens at the first failure-capable operand (returning a
  Result or (value, error) — the latter adapts through result.Of). After
  that, `>=>` binds Result operands and lifts plain operands (Map/Tee),
  while `>>>` demands an operand accepting the Result itself. A chain in
  which no operand can fail is an error — use >>>. Emission is one flat
  capture-once IIFE threading std/result combinators.

  Background:
    Given a module "example.com/demo" using the goplus standard library

  Scenario: A mixed chain lifts every operand shape
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      	"strings"

      	"goforge.dev/goplus/std/result"
      )

      var saved []int

      func validate(s string) result.Result[string, error] {
      	if s == "" {
      		return result.Err[string, error]{Err: fmt.Errorf("empty")}
      	}
      	return result.Ok[string, error]{Value: s}
      }

      func save(n int) { saved = append(saved, n) }

      func unwrap(r result.Result[int, error]) int { return result.UnwrapOr(r, -1) }

      func main() {
      	pipeline := strings.TrimSpace >=> validate >=> strconv.Atoi >=> save >>> unwrap
      	fmt.Println(pipeline(" 21 "))
      	fmt.Println(pipeline(""))
      	fmt.Println(saved)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      21
      -1
      [21]
      """

  Scenario: A (value, error) first operand enters the rail through Of
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"goforge.dev/goplus/std/result"
      )

      func double(n int) int { return n * 2 }

      func main() {
      	parse := strconv.Atoi >=> double
      	fmt.Println(result.UnwrapOr(parse("21"), -1))
      	fmt.Println(result.IsErr(parse("x")))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      42
      true
      """

  Scenario: A Result constructor operand infers its error type from the chain
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"goforge.dev/goplus/std/result"
      )

      func double(n int) int { return n * 2 }

      func main() {
      	f := strconv.Atoi >=> double >=> result.Ok
      	fmt.Println(f("21"))
      	fmt.Println(result.IsErr(f("x")))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "{42}"
    And stdout contains "true"

  Scenario: After the rail opens, >>> requires a Result-accepting operand
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      func double(n int) int { return n * 2 }

      func main() {
      	f := strconv.Atoi >=> double >>> double
      	fmt.Println(f("1"))
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "after a failure-capable operand, >>> requires a stage that accepts the"
    And stderr contains "use >=> to stay on the railway"

  Scenario: A chain in which nothing can fail is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func double(n int) int { return n * 2 }
      func inc(n int) int    { return n + 1 }

      func main() {
      	f := double >=> inc
      	fmt.Println(f(1))
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "no operand of this >=> chain can fail; use >>> for plain composition"

  Scenario: Railway laws hold on sampled inputs
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"goforge.dev/goplus/std/result"
      )

      func parse(s string) result.Result[int, error] {
      	return result.Of(strconv.Atoi(s))
      }

      func nonneg(n int) result.Result[int, error] {
      	if n < 0 {
      		return result.Err[int, error]{Err: fmt.Errorf("negative")}
      	}
      	return result.Ok[int, error]{Value: n}
      }

      func small(n int) result.Result[int, error] {
      	if n > 100 {
      		return result.Err[int, error]{Err: fmt.Errorf("too big")}
      	}
      	return result.Ok[int, error]{Value: n}
      }

      func same(a, b result.Result[int, error]) bool {
      	if result.IsErr(a) != result.IsErr(b) {
      		return false
      	}
      	return result.UnwrapOr(a, -999) == result.UnwrapOr(b, -999)
      }

      func main() {
      	inputs := []string{"7", "-7", "700", "x", "0"}
      	allOK := true
      	for _, s := range inputs {
      		// left identity: lifting a pure value then binding f == f(value)
      		lhs := result.Bind(result.Ok[string, error]{Value: s}, parse)
      		if !same(lhs, parse(s)) {
      			allOK = false
      		}
      		// associativity: (parse >=> nonneg) >=> small == parse >=> (nonneg >=> small)
      		left := (parse >=> nonneg) >=> small
      		right := parse >=> (nonneg >=> small)
      		if !same(left(s), right(s)) {
      			allOK = false
      		}
      		// tee transparency: a tee stage never changes the value
      		teed := parse >=> func(int) {}
      		if !same(teed(s), parse(s)) {
      			allOK = false
      		}
      	}
      	fmt.Println(allOK)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "true"
