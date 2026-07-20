Feature: Total functions
  `total func` declares a function the compiler verifies terminating;
  only total functions are callable inside types. v0.7.0's surface:
  parameters and the single result are `nat` (erased to int), bodies are
  if/return over nat expressions (+ - * and calls to total functions),
  recursion must structurally shrink an argument, and nat subtraction is
  admissible only where the path proves it non-negative. The erased Go
  body behind the //goplus:total marker IS the definition — importers
  re-elaborate it; nothing else is duplicated.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Guarded recursion elaborates, checks, erases, and runs
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      total func Plus(a, b nat) nat {
      	if a == 0 {
      		return b
      	}
      	return Plus(a-1, b) + 1
      }

      total func Double(a nat) nat {
      	return Plus(a, a)
      }

      func main() {
      	fmt.Println(Plus(2, 3), Double(4))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "5 8"
    And the file "main_gp.go" contains:
      """
      //goplus:total Plus(a, b nat) nat
      func Plus(a, b int) int {
      """
    And the file "main_gp.go" contains:
      """
      //goplus:total Double(a nat) nat
      func Double(a int) int {
      """

  Scenario: Totals cross packages through their markers
    Given a Go+ file "arith/arith.gp":
      """
      package arith

      total func Plus(a, b nat) nat {
      	if a == 0 {
      		return b
      	}
      	return Plus(a-1, b) + 1
      }
      """
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"example.com/demo/arith"
      )

      total func Triple(a nat) nat {
      	return arith.Plus(arith.Plus(a, a), a)
      }

      func main() {
      	fmt.Println(Triple(5))
      }
      """
    When I run goplus with arguments "gen ./..."
    Then the exit code is 0
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "15"

  Scenario: A non-shrinking recursive call is rejected
    Given a Go+ file "main.gp":
      """
      package main

      total func Bad(a nat) nat {
      	return Bad(a + 1)
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "total function Bad does not terminate: this recursive call shrinks no argument"

  Scenario: Unguarded nat subtraction is rejected
    Given a Go+ file "main.gp":
      """
      package main

      total func Pred(a nat) nat {
      	return a - 1
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot prove a ≥ 1 here; nat subtraction needs a guard"

  Scenario: A comparison guard justifies subtraction
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      total func Monus(a, b nat) nat {
      	if a >= b {
      		return a - b
      	}
      	return 0
      }

      func main() {
      	fmt.Println(Monus(7, 3), Monus(3, 7))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "4 0"

  Scenario: Total functions take and return nat only
    Given a Go+ file "main.gp":
      """
      package main

      total func F(a string) nat {
      	return 0
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "total functions take and return nat in v0.7.0; a parameter has type string"

  Scenario: Only total functions are callable from a total body
    Given a Go+ file "main.gp":
      """
      package main

      func helper(a int) int { return a }

      total func G(a nat) nat {
      	return G(helper(a))
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "total function G calls helper, which is not a total function"

  Scenario: Statements outside the fragment are rejected
    Given a Go+ file "main.gp":
      """
      package main

      total func F(a nat) nat {
      	for i := 0; i < 3; i++ {
      	}
      	return a
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "outside the total fragment"

  Scenario: A total method is rejected
    Given a Go+ file "main.gp":
      """
      package main

      type Box struct{}

      total func (b Box) F(a nat) nat {
      	return a
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "a total function cannot have a receiver"
