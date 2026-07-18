Feature: Match statements
  match lowers to a type switch over the sealed interface: case heads gain
  instantiated variant types, arms gain binding prologues, and a sealed
  default arm panics on the impossible (nil) value. Arms bind fields
  positionally; a binder names the whole variant value.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: The canonical Option.Map
    Given a G++ file "main.gpp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func (o Option[T]) Map[U any](f func(T) U) Option[U] {
      	match o {
      	case Some(v):
      		return Some(f(v))
      	case None:
      		return None
      	}
      }

      func main() {
      	var o Option[int] = Some(41)
      	var n Option[int] = None
      	fmt.Println(o.Map(strconv.Itoa), n.Map(strconv.Itoa))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "{41} {}"
    And the file "main_gpp.go" contains:
      """
      	switch __gpp_m0 := any(o).(type) {
      	case Some[T]:
      		v := __gpp_m0.Value
      		return Some[U]{Value: f(v)}
      	case None[T]:
      		return None[U]{}
      	default:
      		panic("gpp: impossible enum value in match")
      	}
      """

  Scenario: Binders, field wildcards, and value semantics
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Shape enum {
      	Circle(r float64)
      	Rect(w, h float64)
      	Point
      }

      func describe(s Shape) string {
      	out := ""
      	match s {
      	case Circle(r):
      		out = fmt.Sprint("circle ", r)
      	case c := Rect(w, _):
      		out = fmt.Sprint("rect ", w, " of ", c.H)
      	case Point:
      		out = "point"
      	}
      	return out
      }

      func main() {
      	fmt.Println(describe(Circle(2)))
      	fmt.Println(describe(Rect(3, 4)))
      	fmt.Println(describe(Point))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "circle 2"
    And stdout contains "rect 3 of 4"
    And stdout contains "point"

  Scenario: The wildcard arm becomes the default clause
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Shape enum {
      	Circle(r float64)
      	Rect(w, h float64)
      	Point
      }

      func main() {
      	var s Shape = Rect(1, 2)
      	kind := ""
      	match s {
      	case Circle(_):
      		kind = "circle"
      	case _:
      		kind = "other"
      	}
      	fmt.Println(kind)
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "other"

  Scenario: Matching a cross-package enum by qualified patterns
    Given a G++ file "lib/shape.gpp":
      """
      package lib

      type Shape enum {
      	Circle(r float64)
      	Point
      }
      """
    And a G++ file "main.gpp":
      """
      package main

      import (
      	"fmt"

      	"example.com/demo/lib"
      )

      func main() {
      	var s lib.Shape = lib.Circle(3)
      	match s {
      	case lib.Circle(r):
      		fmt.Println("r =", r)
      	case lib.Point:
      		fmt.Println("point")
      	}
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "r = 3"

  Scenario: Matches nest inside arm bodies
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Coin enum {
      	Heads
      	Tails
      }

      func main() {
      	var a Coin = Heads
      	var b Coin = Tails
      	match a {
      	case Heads:
      		match b {
      		case Heads:
      			fmt.Println("HH")
      		case Tails:
      			fmt.Println("HT")
      		}
      	case Tails:
      		fmt.Println("T?")
      	}
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "HT"

  Scenario: A non-enum scrutinee is an error
    Given a G++ file "main.gpp":
      """
      package main

      type Shape enum {
      	Point
      }

      func main() {
      	x := 5
      	match x {
      	case Point:
      	}
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "match requires an enum-typed scrutinee; x has type int"

  Scenario: A bare break inside an arm is rejected
    Given a G++ file "main.gpp":
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
      		break
      	case Tails:
      	}
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "break is not supported directly inside a match arm"
