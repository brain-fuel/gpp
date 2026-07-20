Feature: Exhaustive matching
  A match must cover every variant that can inhabit the scrutinee's type
  (GADT-impossible variants don't count); 'case _:' is the explicit
  opt-out and must be last. Dead arms — duplicates, GADT-impossible
  patterns — are hard errors, not warnings.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: A missing variant is named in the error
    Given a Go+ file "main.gp":
      """
      package main

      type Shape enum {
      	Circle(r float64)
      	Rect(w, h float64)
      	Point
      }

      func main() {
      	var s Shape = Point
      	match s {
      	case Circle(_):
      	case Point:
      	}
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "non-exhaustive match on Shape: missing Rect(_, _); add the missing cases or a 'case _:' arm"

  Scenario: The wildcard arm opts out of exhaustiveness
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Shape enum {
      	Circle(r float64)
      	Rect(w, h float64)
      	Point
      }

      func main() {
      	var s Shape = Point
      	match s {
      	case Circle(_):
      		fmt.Println("circle")
      	case _:
      		fmt.Println("other")
      	}
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "other"

  Scenario: A duplicate arm is unreachable and rejected
    Given a Go+ file "main.gp":
      """
      package main

      type Coin enum {
      	Heads
      	Tails
      }

      func main() {
      	var c Coin = Heads
      	match c {
      	case Heads:
      	case Tails:
      	case Heads:
      	}
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "unreachable match arm: Heads is already covered by the arms above"

  Scenario: The wildcard must be the last arm
    Given a Go+ file "main.gp":
      """
      package main

      type Coin enum {
      	Heads
      	Tails
      }

      func main() {
      	var c Coin = Heads
      	match c {
      	case _:
      	case Heads:
      	}
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "'case _:' must be the last arm of a match"

  Scenario: GADT-impossible variants are excluded from the universe
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	Truth(b bool) Expr[bool]
      	Pair(l, r int)
      }

      func evalInt(e Expr[int]) int {
      	match e {
      	case Lit(v):
      		return v
      	case Pair(l, r):
      		return l + r
      	}
      }

      func main() {
      	fmt.Println(evalInt(Lit(7)) + evalInt(Pair(1, 2)))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "10"

  Scenario: A GADT-impossible arm is a hard error
    Given a Go+ file "main.gp":
      """
      package main

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	Truth(b bool) Expr[bool]
      }

      func evalInt(e Expr[int]) int {
      	match e {
      	case Lit(v):
      		return v
      	case Truth(_):
      		return 0
      	}
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "pattern Truth(_) can never match a value of type Expr[int]: Truth constructs Expr[bool]"
