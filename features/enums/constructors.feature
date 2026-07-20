Feature: Constructing enum values
  Constructors are call-style (Some(41)) or bare (None), lowered to
  named-field composite literals. Type arguments come from explicit
  instantiation, the expected type of the context, or unification of
  declared parameter types with argument types; bare names shared by
  several enums are disambiguated by the same inference, and only genuinely
  ambiguous uses must qualify. In function-value position a constructor
  auto-wraps into a closure.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Arguments alone determine the type arguments
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func main() {
      	s := Some(41)
      	fmt.Println(s.Value + 1)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "42"
    And the file "main_gp.go" contains:
      """
      s := Some[int]{Value: 41}
      """

  Scenario: The expected type flows through declarations, returns, and elements
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func pick(ok bool) Option[string] {
      	if ok {
      		return Some("yes")
      	}
      	return None
      }

      func main() {
      	var o Option[int] = None
      	xs := []Option[int]{Some(1), None}
      	fmt.Println(o == None, len(xs), pick(true))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "true 2 {yes}"
    And the file "main_gp.go" contains:
      """
      var o Option[int] = None[int]{}
      """
    And the file "main_gp.go" contains:
      """
      xs := []Option[int]{Some[int]{Value: 1}, None[int]{}}
      """

  Scenario: Recursive constructor literals resolve outside-in
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type List[T any] enum {
      	Cons(head T, tail List[T])
      	Nil
      }

      func sum(l List[int]) int {
      	total := 0
      	for {
      		c, ok := any(l).(Cons[int])
      		if !ok {
      			return total
      		}
      		total += c.Head
      		l = c.Tail
      	}
      }

      func main() {
      	var l List[int] = Cons(1, Cons(2, Cons(3, Nil)))
      	fmt.Println(sum(l))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "6"
    And the file "main_gp.go" contains:
      """
      var l List[int] = Cons[int]{Head: 1, Tail: Cons[int]{Head: 2, Tail: Cons[int]{Head: 3, Tail: Nil[int]{}}}}
      """

  Scenario: Explicit instantiation and enum-qualified constructors
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func main() {
      	a := Some[string]("hi")
      	b := Option[int].None
      	c := Option[string].Some("q")
      	fmt.Println(a.Value, b, c.Value)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "hi {} q"
    And the file "main_gp.go" contains:
      """
      b := None[int]{}
      """

  Scenario: A constructor in function position auto-wraps into a closure
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func apply(x int, f func(int) Option[int]) Option[int] {
      	return f(x)
      }

      func main() {
      	fmt.Println(apply(7, Some))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "{7}"
    And the file "main_gp.go" contains:
      """
      apply(7, func(p0 int) Option[int] { return Some[int]{Value: p0} })
      """

  Scenario: Ground GADT constructors need no inference
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	If(c bool, t, e Expr[T])
      }

      func main() {
      	l := Lit(7)
      	var e Expr[int] = If(true, Lit(1), Lit(2))
      	fmt.Println(l.V, e != nil)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "7 true"
    And the file "main_gp.go" contains:
      """
      l := Lit{V: 7}
      """
    And the file "main_gp.go" contains:
      """
      var e Expr[int] = If[int]{C: true, T: Lit{V: 1}, E: Lit{V: 2}}
      """

  Scenario: Inference disambiguates a variant name shared by two enums
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      type List[T any] enum {
      	Cons(head T, tail List[T])
      	None
      }

      func main() {
      	var o Option[int] = None
      	var l List[int] = None
      	fmt.Println(o, l)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "{} {}"
    And the file "main_gp.go" contains:
      """
      var o Option[int] = OptionNone[int]{}
      """
    And the file "main_gp.go" contains:
      """
      var l List[int] = ListNone[int]{}
      """

  Scenario: A genuinely ambiguous bare constructor must qualify
    Given a Go+ file "main.gp":
      """
      package main

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      type List[T any] enum {
      	Cons(head T, tail List[T])
      	None
      }

      func main() {
      	x := None
      	_ = x
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "constructor None is declared by Option and List; qualify it"

  Scenario: An uninferable constructor points at the fixes
    Given a Go+ file "main.gp":
      """
      package main

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func main() {
      	x := None
      	_ = x
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot infer the type arguments of constructor None"

  Scenario: Constructors work across modules from markers alone, toolchain-free
    Given a file "dep/go.mod":
      """
      module example.com/dep

      go 1.24
      """
    And a Go+ file "dep/lib/option.gp":
      """
      package lib

      type Option[T any] enum {
      	Some(value T)
      	None
      }
      """
    And I run goplus in "dep" with arguments "gen ./..."
    And the file "dep/lib/option.gp" is deleted
    And a file "app/go.mod":
      """
      module example.com/app

      go 1.24

      require example.com/dep v0.0.0

      replace example.com/dep => ../dep
      """
    And a Go+ file "app/main.gp":
      """
      package main

      import (
      	"fmt"

      	"example.com/dep/lib"
      )

      func main() {
      	s := lib.Some(41)
      	var n lib.Option[string] = lib.Option[string].None
      	fmt.Println(s.Value, n)
      }
      """
    When I run goplus in "app" with arguments "run ."
    Then the exit code is 0
    And stdout contains "41 {}"
    And the file "app/main_gp.go" contains:
      """
      s := lib.Some[int]{Value: 41}
      """
    And the file "app/main_gp.go" contains:
      """
      var n lib.Option[string] = lib.None[string]{}
      """
