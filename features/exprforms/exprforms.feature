Feature: Expression-oriented if, switch, and match
  Expression if/switch/match hoist to statements before their anchor
  statement: a type-deferred temp is declared, each arm assigns it, and the
  expression site reads the temp. The temp's type is the context's expected
  type first, otherwise the arms' shared default type. Hoisted sites
  evaluate before the rest of their statement, in source order.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: An if expression lowers to a hoisted statement
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func main() {
      	x := 3
      	y := if x > 2 { "big" } else { "small" }
      	fmt.Println(y)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "big"
    And the file "main_gp.go" contains:
      """
      	var __gp_v0 string
      	if x > 2 {
      		__gp_v0 = "big"
      	} else {
      		__gp_v0 = "small"
      	}
      	y := __gp_v0
      """

  Scenario: A switch expression with a tag and multi-value cases
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func main() {
      	x := 3
      	n := switch x {
      	case 1:
      		10
      	case 2, 3:
      		20
      	default:
      		0
      	}
      	fmt.Println(n)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "20"
    And the file "main_gp.go" contains:
      """
      	var __gp_v0 int
      	switch x {
      	case 1:
      		__gp_v0 = 10
      	case 2, 3:
      		__gp_v0 = 20
      	default:
      		__gp_v0 = 0
      	}
      	n := __gp_v0
      """

  Scenario: A match expression reuses the whole match machinery
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Shape enum {
      	Circle(r float64)
      	Rect(w, h float64)
      }

      func area(s Shape) float64 {
      	return match s {
      	case Circle(r):
      		3.14 * r * r
      	case Rect(w, h):
      		w * h
      	}
      }

      func main() {
      	fmt.Println(area(Circle(2)), area(Rect(3, 4)))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "12.56 12"
    And the file "main_gp.go" contains:
      """
      	var __gp_v0 float64
      	switch __gp_m0 := any(s).(type) {
      	case Circle:
      		r := __gp_m0.R
      		__gp_v0 = 3.14 * r * r
      	case Rect:
      		w := __gp_m0.W
      		h := __gp_m0.H
      		__gp_v0 = w * h
      	default:
      		panic("goplus: impossible enum value in match")
      	}
      	return __gp_v0
      """

  Scenario: A non-exhaustive match expression is an error
    Given a Go+ file "main.gp":
      """
      package main

      type Shape enum {
      	Circle(r float64)
      	Rect(w, h float64)
      }

      func area(s Shape) float64 {
      	return match s {
      	case Circle(r):
      		3.14 * r * r
      	}
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "non-exhaustive match"
    And stderr contains "Rect"

  Scenario: GADT-refined match-expression arms are wrapped for erasure
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Lit(n int) Expr[int]
      	Str(s string) Expr[string]
      }

      func eval[T any](e Expr[T]) T {
      	return match e {
      	case Lit(n):
      		n
      	case Str(s):
      		s
      	}
      }

      func main() {
      	fmt.Println(eval(Lit(21))*2, eval(Str("hi")))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "42 hi"
    And the file "main_gp.go" contains:
      """
      	var __gp_v0 T
      	switch __gp_m0 := any(e).(type) {
      	case Lit:
      		n := __gp_m0.N
      		__gp_v0 = any(n).(T)
      	case Str:
      		s := __gp_m0.S
      		__gp_v0 = any(s).(T)
      	default:
      		panic("goplus: impossible enum value in match")
      	}
      	return __gp_v0
      """

  Scenario: The context's expected type wins over the arms' default type
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func main() {
      	c := true
      	var f float64 = if c { 1 } else { 2 }
      	fmt.Println(f + 0.5)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "1.5"
    And the file "main_gp.go" contains:
      """
      	var __gp_v0 float64
      """

  Scenario: Mismatched arm types without a determining context are an error
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func main() {
      	c := true
      	x := if c { 1 } else { "s" }
      	fmt.Println(x)
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "main.gp:7:"
    And stderr contains "mismatched arm types in this expression form: int vs string"

  Scenario: An expression switch without a default arm is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func main() {
      	x := 1
      	n := switch x {
      	case 1:
      		10
      	}
      	fmt.Println(n)
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "an expression switch must have a default arm"

  Scenario: Expression forms nest, and arms hoist inside their own arm
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func main() {
      	x := 5
      	y := if x > 0 { if x > 3 { "big" } else { "mid" } } else { "neg" }
      	z := switch x {
      	case 5:
      		if x > 4 { 100 } else { 50 }
      	default:
      		0
      	}
      	fmt.Println(y, z)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "big 100"

  Scenario: Hoisted sites evaluate before the rest of their statement, in source order
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func step(n int) int {
      	fmt.Println("eval", n)
      	return n
      }

      func main() {
      	fmt.Println(step(1), if step(2) > 0 { step(3) } else { -1 }, if step(4) > 0 { step(5) } else { -1 })
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      eval 2
      eval 3
      eval 4
      eval 5
      eval 1
      1 3 5
      """

  Scenario: An expression form in a for condition is an error
    Given a Go+ file "main.gp":
      """
      package main

      func main() {
      	n := 0
      	for n < if true { 3 } else { 5 } {
      		n++
      	}
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot appear in a for condition or post statement"

  Scenario: An expression form in an else-if condition is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func main() {
      	a := false
      	if a {
      		fmt.Println("a")
      	} else if (if true { 1 } else { 2 }) > 0 {
      		fmt.Println("b")
      	}
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot appear in an else-if condition"

  Scenario: An expression form on the right of && is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func main() {
      	a := false
      	if a && (if true { 1 } else { 2 }) > 0 {
      		fmt.Println("x")
      	}
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot appear on the right side of &&"

  Scenario: An expression form in a statement-switch case value is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func main() {
      	x := 1
      	switch x {
      	case if true { 1 } else { 2 }:
      		fmt.Println("one")
      	}
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot appear in a case value"

  Scenario: An expression form at package level is an error
    Given a Go+ file "main.gp":
      """
      package main

      var x = if true { 1 } else { 2 }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "use an init function for package-level values"
