Feature: Bounded existential variants
  A variant may bind existential type variables CONSTRAINED by an
  interface: `Packed[A fmt.Stringer, B error](x A, y A, e B)`. Erasure
  happens at the boundary — struct fields, lowered constructors, and
  match binders are typed at the bound; two fields sharing an existential
  variable lose the same-dynamic-type fact. An unbounded variable is a
  compile error: Go cannot express a match arm generic in a hidden type.
  Existential variables must not appear in the result type and must be
  used by at least one field.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Erasure at the boundary — construct, store, match
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Row[T any] enum {
      	Cell(v T)
      	Packed[A fmt.Stringer, B error](x A, y A, e B, tag string)
      }

      type mins int

      func (m mins) String() string { return fmt.Sprintf("%dm", int(m)) }

      func describe(r Row[int]) string {
      	match r {
      	case Cell(v):
      		return fmt.Sprint("cell:", v)
      	case Packed(x, y, e, tag):
      		return tag + ":" + x.String() + "/" + y.String() + "/" + e.Error()
      	}
      }

      func main() {
      	fmt.Println(describe(Cell(7)))
      	fmt.Println(describe(Packed[int](mins(3), mins(9), fmt.Errorf("boom"), "p")))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      cell:7
      p:3m/9m/boom
      """
    And the file "main_gp.go" contains:
      """
      //goplus:variant (Row[T]) Packed[A fmt.Stringer, B error](x A, y A, e B, tag string)
      type Packed[T any] struct {
      	X   fmt.Stringer
      	Y   fmt.Stringer
      	E   error
      	Tag string
      }
      """

  Scenario: Existential diagnostics
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Row[T any] enum {
      	A1[X any](v X)
      	A2[X fmt.Stringer](v X) Row[X]
      	A3[X fmt.Stringer](v int)
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "existential type parameter X of variant A1 must have a plain interface bound: Go cannot express a match arm generic in a hidden type"
    And stderr contains "existential type parameter X of variant A2 must not appear in the result type; existentials are erased at the constructor boundary"
    And stderr contains "existential type parameter X of variant A3 is not used by any field"

  Scenario: Existential enums cross packages through markers
    Given a Go+ file "lib/lib.gp":
      """
      package lib

      import "fmt"

      type Box enum {
      	Shown[A fmt.Stringer](v A)
      	Empty
      }
      """
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"example.com/demo/lib"
      )

      type secs int

      func (s secs) String() string { return fmt.Sprintf("%ds", int(s)) }

      func main() {
      	var b lib.Box = lib.Shown(secs(4))
      	match b {
      	case lib.Shown(v):
      		fmt.Println("shown", v.String())
      	case lib.Empty:
      		fmt.Println("empty")
      	}
      }
      """
    When I run goplus with arguments "gen ./..."
    Then the exit code is 0
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "shown 4s"
