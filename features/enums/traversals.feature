Feature: Derived deep traversals
  Every SELF-RECURSIVE monomorphic enum derives, by default, three deep
  traversals alongside its fold: <Enum>Children (direct same-enum
  subterms), <Enum>Universe (the node plus all transitive subterms,
  preorder, as an iter.Seq), and <Enum>Transform (bottom-up rewrite).
  Traversal names are always enum-prefixed. Descent sees through
  same-package struct wrappers whose fields (transitively) hold the enum
  — a binder wrapper like Scope{Name string; Body Tm} is glass, not a
  wall — and through slices of the enum or of wrappers. Enums that are
  not self-recursive, are generic or indexed, or carry `//goplus:derive
  off` derive no traversals. Field shapes outside the descendable set
  (func fields, imported types, maps) are simply not descended: a
  traversal covers the reachable enum spine.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: A self-recursive enum derives Children, Universe, and Transform
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Tm enum {
      	Lit(n int)
      	Add(l Tm, r Tm)
      }

      func main() {
      	t := Add(Add(Lit(1), Lit(2)), Lit(3))
      	fmt.Println(len(TmChildren(t)))
      	count := 0
      	for range TmUniverse(t) {
      		count++
      	}
      	fmt.Println(count)
      	doubled := TmTransform(t, func(u Tm) Tm {
      		match u {
      		case Lit(n):
      			return Lit(2 * n)
      		case _:
      			return u
      		}
      	})
      	sum := 0
      	for u := range TmUniverse(doubled) {
      		match u {
      		case Lit(n):
      			sum += n
      		case _:
      		}
      	}
      	fmt.Println(sum)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      2
      5
      12
      """
    And the file "main_gp.go" contains:
      """
      // TmChildren lists the direct Tm subterms of t.
      func TmChildren(t Tm) []Tm {
      """
    And the file "main_gp.go" contains:
      """
      // TmUniverse yields t and all transitive Tm subterms, preorder.
      func TmUniverse(t Tm) iter.Seq[Tm] {
      """
    And the file "main_gp.go" contains:
      """
      // TmTransform rewrites t bottom-up: children first, then f at each node.
      func TmTransform(t Tm, f func(Tm) Tm) Tm {
      """

  Scenario: Descent sees through a same-package struct wrapper
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Scope struct {
      	Name string
      	Body Tm
      }

      type Tm enum {
      	Var(name string)
      	Lam(scope Scope)
      	App(fn Tm, arg Tm)
      }

      func main() {
      	t := Lam(Scope{Name: "x", Body: App(Var("x"), Var("y"))})
      	fmt.Println(len(TmChildren(t)))
      	count := 0
      	for range TmUniverse(t) {
      		count++
      	}
      	fmt.Println(count)
      	renamed := TmTransform(t, func(u Tm) Tm {
      		match u {
      		case Var(name):
      			if name == "y" {
      				return Var("z")
      			}
      			return u
      		case _:
      			return u
      		}
      	})
      	match renamed {
      	case Lam(scope):
      		fmt.Println(scope.Name)
      		match scope.Body {
      		case App(_, arg):
      			match arg {
      			case Var(name):
      				fmt.Println(name)
      			case _:
      			}
      		case _:
      		}
      	case _:
      	}
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      1
      4
      x
      z
      """

  Scenario: Slice fields descend element-wise and Transform copies, never mutates
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Tm enum {
      	Lit(n int)
      	Call(fn Tm, args []Tm)
      }

      func main() {
      	var t Tm = Call(Lit(0), []Tm{Lit(1), Lit(2)})
      	fmt.Println(len(TmChildren(t)))
      	out := TmTransform(t, func(u Tm) Tm {
      		match u {
      		case Lit(n):
      			return Lit(n + 10)
      		case _:
      			return u
      		}
      	})
      	match t {
      	case Call(_, args):
      		match args[0] {
      		case Lit(n):
      			fmt.Println(n)
      		case _:
      		}
      	case _:
      	}
      	match out {
      	case Call(_, args):
      		match args[1] {
      		case Lit(n):
      			fmt.Println(n)
      		case _:
      		}
      	case _:
      	}
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      3
      1
      12
      """

  Scenario: Non-recursive, generic, and opted-out enums derive no traversals
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Color enum {
      	Red
      	Green
      }

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      //goplus:derive off
      type Expr enum {
      	Num(n int)
      	Neg(e Expr)
      }

      func main() {
      	fmt.Println("ok")
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And the file "main_gp.go" does not contain "ColorChildren"
    And the file "main_gp.go" does not contain "OptionChildren"
    And the file "main_gp.go" does not contain "ExprChildren"

  Scenario: Nil optional fields are skipped, never handed to the rewrite
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Tm enum {
      	Lit(n int)
      	Let(ty Tm, v Tm)
      }

      func main() {
      	var t Tm = Let(nil, Lit(1))
      	fmt.Println(len(TmChildren(t)))
      	count := 0
      	for range TmUniverse(t) {
      		count++
      	}
      	fmt.Println(count)
      	out := TmTransform(t, func(u Tm) Tm {
      		match u {
      		case Lit(n):
      			return Lit(n + 1)
      		case _:
      			return u
      		}
      	})
      	match out {
      	case Let(ty, v):
      		fmt.Println(ty == nil)
      		match v {
      		case Lit(n):
      			fmt.Println(n)
      		case _:
      		}
      	case _:
      	}
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      1
      2
      true
      2
      """
