Feature: QTT usage checking
  Declared quantities are enforced: a 0-parameter never appears at
  runtime (types and index terms erase, so they are fine); a linear
  (1) parameter is consumed exactly once on every path — branches must
  agree, loops are out, closure capture is the consumption; a
  multiplicity variable ([m mult]) admits 0, so at most one use per
  path. Multiplicity binders erase from the generated type parameters.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Balanced linear use and multiplicity polymorphism generate
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strings"
      )

      func Consume(1 b *strings.Builder, c bool) string {
      	if c {
      		return b.String()
      	}
      	return b.String()
      }

      func Poly[m mult, T any](m x T, use func(T)) {
      	use(x)
      }

      func main() {
      	var b strings.Builder
      	fmt.Println(Consume(&b, false) == "")
      	Poly(7, func(n int) { fmt.Println(n) })
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      true
      7
      """
    And the file "main_gp.go" contains:
      """
      //goplus:dep Poly[m mult, T any](m x T, use func(T))
      func Poly[T any](x T, use func(T)) {
      """

  Scenario: A 0-parameter cannot be used at runtime
    Given a Go+ file "main.gp":
      """
      package main

      func F(0 n nat, x int) int {
      	return x + n
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "parameter n has quantity 0: it exists only at check time and cannot be used at runtime"

  Scenario: A linear parameter consumed twice is rejected
    Given a Go+ file "main.gp":
      """
      package main

      import "strings"

      func Twice(1 b *strings.Builder) {
      	b.Reset()
      	b.Reset()
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "linear parameter b is consumed more than once on some path"

  Scenario: A linear parameter never consumed is rejected
    Given a Go+ file "main.gp":
      """
      package main

      import "strings"

      func Drop(1 b *strings.Builder) {
      	_ = 1
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "linear parameter b is never consumed"

  Scenario: Branches must agree on linear consumption
    Given a Go+ file "main.gp":
      """
      package main

      import "strings"

      func Branchy(1 b *strings.Builder, c bool) {
      	if c {
      		b.Reset()
      	}
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "the branches of an if consume it a different number of times"

  Scenario: Linear use inside a loop is rejected
    Given a Go+ file "main.gp":
      """
      package main

      import "strings"

      func Loopy(1 b *strings.Builder) {
      	for i := 0; i < 2; i++ {
      		b.Reset()
      	}
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "it is consumed inside a loop, which may run any number of times"

  Scenario: An unknown quantity name is rejected
    Given a Go+ file "main.gp":
      """
      package main

      func F[T any](q x T) {
      	_ = x
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "quantity q of parameter x is not 0, 1, or a declared multiplicity variable ([q mult])"
