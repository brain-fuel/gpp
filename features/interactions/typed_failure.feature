Feature: Typed-failure features compose with the rest of Go+
  The v0.4.0 constructs nest: railway pipelines can be match-expression
  arms, ? early-returns work inside chain-mode (nested-pattern) match
  arms, and expression conditionals can head a pipeline.

  Background:
    Given a module "example.com/demo" using the goplus standard library

  Scenario: A railway pipeline as a match-expression arm
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      	"strings"

      	"goforge.dev/goplus/std/result"
      )

      type Source enum {
      	Inline(text string)
      	Def(value int)
      }

      func parse(s string) result.Result[int, error] {
      	return result.Of(strconv.Atoi(s))
      }

      func load(src Source) int {
      	return match src {
      	case Inline(t):
      		t |> strings.TrimSpace |> parse |> .UnwrapOr(-1)
      	case Def(v):
      		v
      	}
      }

      func main() {
      	var a Source = Inline(" 21 ")
      	var b Source = Def(7)
      	var c Source = Inline("bad")
      	fmt.Println(load(a), load(b), load(c))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "21 7 -1"

  Scenario: ? inside a chain-mode match arm early-returns from the function
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      	"strings"
      )

      type Source enum {
      	Inline(text string)
      	Def(value int)
      }

      type Wrap enum {
      	One(s Source)
      	Zero
      }

      func firstNum(w Wrap) (int, error) {
      	match w {
      	case One(Inline(t)):
      		n := strconv.Atoi(strings.TrimSpace(t))?
      		return n, nil
      	case One(Def(v)):
      		return v, nil
      	case Zero:
      		return 0, nil
      	}
      }

      func main() {
      	var w Wrap = One(Inline(" 5 "))
      	fmt.Println(firstNum(w))
      	var bad Wrap = One(Inline("x"))
      	_, err := firstNum(bad)
      	fmt.Println(err != nil)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "5 <nil>"
    And stdout contains "true"

  Scenario: An expression if heads a pipeline
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func double(n int) int { return n * 2 }

      func pick(c bool) int {
      	return if c { 10 } else { 20 } |> double
      }

      func main() {
      	fmt.Println(pick(true), pick(false))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "20 40"
