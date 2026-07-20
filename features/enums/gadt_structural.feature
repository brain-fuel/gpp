Feature: Structural GADT result types
  A variant's result type may apply the enum to ARBITRARY type
  expressions: Expr[[]T], Expr[map[string]T], cross-position Foo[U, T].
  The variant struct's type parameters are exactly the enum parameters
  OCCURRING in the result arguments; case heads, constructor inference,
  possibility filtering, and exhaustiveness all reduce to structural
  unification of the result patterns against the scrutinee's type
  arguments. When the scrutinee's argument is a bare type parameter and
  the variant's is composite, Go's erasure cannot name the case head:
  the variant still counts toward exhaustiveness but an explicit arm is
  an error.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Composite result arguments construct, match, and filter
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	Sliced(vs []int) Expr[[]int]
      	Wrap(inner Expr[T]) Expr[[]T]
      	Pairy(a T, b string) Expr[map[string]T]
      }

      func demo(e Expr[[]int]) string {
      	match e {
      	case Sliced(vs):
      		return fmt.Sprint("sliced", vs)
      	case Wrap(inner):
      		_ = inner
      		return "wrap"
      	}
      }

      func main() {
      	var a Expr[[]int] = Sliced([]int{1, 2})
      	fmt.Println(demo(a))
      	fmt.Println(demo(Wrap[int](Lit(1))))
      	var m Expr[map[string]bool] = Pairy(true, "k")
      	_ = m
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      sliced[1 2]
      wrap
      """
    And the file "main_gp.go" contains:
      """
      	case Wrap[int]:
      """

  Scenario: Impossible composite variants make a wildcard unreachable
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	Sliced(vs []int) Expr[[]int]
      }

      func f(e Expr[[]int]) int {
      	match e {
      	case Sliced(vs):
      		return len(vs)
      	case _:
      		return 0
      	}
      }

      func main() { fmt.Println(f(Sliced(nil))) }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "unreachable match arm"

  Scenario: Cross-position type parameters swap through the result type
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Duo[A any, B any] enum {
      	Straight(a A, b B)
      	Flipped(a A, b B) Duo[B, A]
      }

      func read(d Duo[int, string]) string {
      	match d {
      	case Straight(a, b):
      		return fmt.Sprint("s:", a, b)
      	case Flipped(a, b):
      		return fmt.Sprint("f:", a, b)
      	}
      }

      func main() {
      	fmt.Println(read(Straight(1, "x")))
      	var d Duo[int, string] = Flipped("y", 2)
      	fmt.Println(read(d))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "s:1x"
    And stdout contains "f:y2"
    And the file "main_gp.go" contains:
      """
      	case Flipped[string, int]:
      """

  Scenario: A composite variant on a generic scrutinee is unmatchable
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Plain(v T)
      	Wrap(inner Expr[T]) Expr[[]T]
      }

      func f[U any](e Expr[U]) string {
      	match e {
      	case Plain(v):
      		return fmt.Sprint(v)
      	case Wrap(inner):
      		_ = inner
      		return "wrap"
      	}
      }

      func main() { fmt.Println(f(Plain(1))) }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot be matched against"
    And stderr contains "do not determine the variant's type parameters under Go's erasure"

  Scenario: The wildcard covers unmatchable composite variants
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Plain(v T)
      	Wrap(inner Expr[T]) Expr[[]T]
      }

      func f[U any](e Expr[U]) string {
      	match e {
      	case Plain(v):
      		return fmt.Sprint(v)
      	case _:
      		return "other"
      	}
      }

      func main() {
      	fmt.Println(f(Plain(1)))
      	fmt.Println(f[[]int](Wrap[int](Plain(2))))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      1
      other
      """
