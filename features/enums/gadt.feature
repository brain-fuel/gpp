Feature: Nested patterns and GADT refinement
  Constructor patterns compose (Add(Lit(a), Lit(b))); a match containing
  nested patterns lowers to an order-preserving assert chain. GADT variants
  refine the scrutinee's type parameters inside their arms: returning a
  T-typed value from an arm that pins T lowers through any(x).(T), made
  total by sealing. Exhaustiveness is Maranget usefulness, so nested
  non-coverage is caught with a witness.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: The canonical typed interpreter
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	Truth(b bool) Expr[bool]
      	Add(l, r Expr[int]) Expr[int]
      	If(c Expr[bool], then, els Expr[T])
      }

      func Eval[T any](e Expr[T]) T {
      	match e {
      	case Lit(v):
      		return v
      	case Truth(b):
      		return b
      	case Add(l, r):
      		return Eval(l) + Eval(r)
      	case If(c, t, f):
      		if Eval(c) {
      			return Eval(t)
      		}
      		return Eval(f)
      	}
      }

      func main() {
      	var prog Expr[int] = If(Truth(true), Add(Lit(40), Lit(2)), Lit(0))
      	fmt.Println(Eval(prog))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "42"
    And the file "main_gpp.go" contains:
      """
      return any(v).(T)
      """
    And the file "main_gpp.go" contains:
      """
      return any(Eval(l) + Eval(r)).(T)
      """

  Scenario: Nested patterns match structurally, in order
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Expr enum {
      	Lit(v int)
      	Add(l, r Expr)
      }

      func describe(e Expr) string {
      	out := ""
      	match e {
      	case Add(Lit(a), Lit(b)):
      		out = fmt.Sprint("const-fold ", a+b)
      	case Add(l, _):
      		_ = l
      		out = "add"
      	case Lit(v):
      		out = fmt.Sprint("lit ", v)
      	}
      	return out
      }

      func main() {
      	fmt.Println(describe(Add(Lit(1), Lit(2))))
      	fmt.Println(describe(Add(Add(Lit(1), Lit(2)), Lit(3))))
      	fmt.Println(describe(Lit(9)))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "const-fold 3"
    And stdout contains "add"
    And stdout contains "lit 9"

  Scenario: Nullary constructors nest as patterns
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type List[T any] enum {
      	Cons(head T, tail List[T])
      	Nil
      }

      func last(l List[int]) int {
      	match l {
      	case Cons(x, Nil):
      		return x
      	case Cons(_, rest):
      		return last(rest)
      	case Nil:
      		return -1
      	}
      }

      func main() {
      	fmt.Println(last(Cons(1, Cons(2, Cons(3, Nil)))))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "3"

  Scenario: Nested non-coverage yields a witness
    Given a G++ file "main.gpp":
      """
      package main

      type Expr enum {
      	Lit(v int)
      	Add(l, r Expr)
      }

      func f(e Expr) {
      	match e {
      	case Add(Lit(a), _):
      		_ = a
      	case Lit(_):
      	}
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "non-exhaustive match on Expr: missing Add(Add(_, _), Lit(_)); add the missing cases or a 'case _:' arm"

  Scenario: An arm covered by earlier nested arms is unreachable
    Given a G++ file "main.gpp":
      """
      package main

      type Expr enum {
      	Lit(v int)
      	Add(l, r Expr)
      }

      func f(e Expr) {
      	match e {
      	case Add(_, _):
      	case Add(Lit(a), _):
      		_ = a
      	case Lit(_):
      	}
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "unreachable match arm: Add(Lit(_), _) is already covered by the arms above"

  Scenario: A naked return inside a refined arm works via named results
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """
    And a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	Other
      }

      func eval[T any](e Expr[T]) (out T) {
      	match e {
      	case Lit(v):
      		out = v
      		return
      	case Other:
      		return
      	}
      }

      func main() {
      	fmt.Println(eval(Lit(9)))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "9"
    And the file "main_gpp.go" contains:
      """
      		out = any(v).(T)
      """

  Scenario: Refinement composes with match inside generic enum methods
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func (o Option[T]) UnwrapOr(fallback T) T {
      	match o {
      	case Some(v):
      		return v
      	case None:
      		return fallback
      	}
      }

      func main() {
      	var o Option[int] = Some(41)
      	var n Option[int] = None
      	fmt.Println(o.UnwrapOr(0) + n.UnwrapOr(1))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "42"
