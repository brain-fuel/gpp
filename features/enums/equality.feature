Feature: Derived structural equality
  Every monomorphic enum derives, by default, structural equality:
  <Enum>Equal (variant-wise, field-wise, recursive through enum fields,
  same-package wrappers, and slices) and <Enum>EqualWith, which threads
  a <Enum>EqOverrides struct of optional per-variant hooks. A hook
  returns (eq, handled); handled=false falls through to the derived
  comparison — proof-irrelevance skips become explicit overrides on a
  derived base. Names are always enum-prefixed. Enums with func-, map-,
  or chan-typed content anywhere in their reachable spine are
  UNDERIVABLE and silently derive no equality, as are generic and
  indexed enums and `//gpp:derive off` enums; a field typed as another
  same-package enum recurses through that enum's derived equality and
  inherits its underivability.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: A recursive enum derives structural equality
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Tm enum {
      	Lit(n int)
      	Add(l Tm, r Tm)
      }

      func main() {
      	a := Add(Lit(1), Lit(2))
      	b := Add(Lit(1), Lit(2))
      	c := Add(Lit(1), Lit(3))
      	fmt.Println(TmEqual(a, b))
      	fmt.Println(TmEqual(a, c))
      	fmt.Println(TmEqual(Lit(1), Add(Lit(1), Lit(1))))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      true
      false
      false
      """
    And the file "main_gpp.go" contains:
      """
      // TmEqual reports structural equality of a and b.
      func TmEqual(a, b Tm) bool {
      """
    And the file "main_gpp.go" contains:
      """
      // TmEqOverrides carries optional per-variant hooks for TmEqualWith.
      """

  Scenario: An override makes a field proof-irrelevant
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Tm enum {
      	Lit(n int)
      	Cast(a Tm, b Tm, x Tm, p Tm)
      }

      func main() {
      	c1 := Cast(Lit(1), Lit(2), Lit(3), Lit(97))
      	c2 := Cast(Lit(1), Lit(2), Lit(3), Lit(42))
      	fmt.Println(TmEqual(c1, c2))
      	irrelevant := TmEqOverrides{
      		Cast: func(x, y Cast) (bool, bool) {
      			return TmEqual(x.A, y.A) && TmEqual(x.B, y.B) && TmEqual(x.X, y.X), true
      		},
      	}
      	fmt.Println(TmEqualWith(c1, c2, irrelevant))
      	c3 := Cast(Lit(9), Lit(2), Lit(3), Lit(42))
      	fmt.Println(TmEqualWith(c1, c3, irrelevant))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      false
      true
      false
      """

  Scenario: Equality descends wrappers and slices
    Given a G++ file "main.gpp":
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
      	Call(fn Tm, args []Tm)
      }

      func main() {
      	l1 := Lam(Scope{Name: "x", Body: Var("x")})
      	l2 := Lam(Scope{Name: "x", Body: Var("x")})
      	l3 := Lam(Scope{Name: "y", Body: Var("x")})
      	fmt.Println(TmEqual(l1, l2))
      	fmt.Println(TmEqual(l1, l3))
      	k1 := Call(Var("f"), []Tm{Var("a"), Var("b")})
      	k2 := Call(Var("f"), []Tm{Var("a"), Var("b")})
      	k3 := Call(Var("f"), []Tm{Var("a")})
      	fmt.Println(TmEqual(k1, k2))
      	fmt.Println(TmEqual(k1, k3))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      true
      false
      true
      false
      """

  Scenario: Func-typed content and its dependents are underivable
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Thunk enum {
      	Done(n int)
      	Suspend(run func() int)
      }

      type Val enum {
      	Num(n int)
      	Closure(t Thunk)
      }

      type Color enum {
      	Red
      	Green
      }

      func main() {
      	var r Color = Red
      	var g Color = Green
      	fmt.Println(ColorEqual(r, r))
      	fmt.Println(ColorEqual(r, g))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      true
      false
      """
    And the file "main_gpp.go" does not contain "ThunkEqual"
    And the file "main_gpp.go" does not contain "ValEqual"
