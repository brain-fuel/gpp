Feature: Enums compose with the rest of Go+
  Enums, constructors, match, enum methods, and v0.1.0 generic methods are
  one language: chains mix them freely, promotion reaches enum methods
  through embedded fields, and enums flow through generic containers.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Constructor, enum-method, and chained calls interleave
    Given a Go+ file "main.gp":
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

      func (o Option[T]) UnwrapOr(fallback T) T {
      	match o {
      	case Some(v):
      		return v
      	case None:
      		return fallback
      	}
      }

      func main() {
      	got := Some(41).Map(strconv.Itoa).Map(func(s string) string { return s + "!" }).UnwrapOr("?")
      	fmt.Println(got)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "41!"

  Scenario: Enum methods promote through embedded fields
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Status enum {
      	Ready
      	Busy(task string)
      }

      func (s Status) Label() string {
      	match s {
      	case Ready:
      		return "ready"
      	case Busy(t):
      		return "busy: " + t
      	}
      }

      type Widget struct {
      	Status
      	name string
      }

      func main() {
      	w := Widget{Status: Busy("forging"), name: "w1"}
      	fmt.Println(w.Label())
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "busy: forging"

  Scenario: Enums flow through v0.1.0 generic containers
    Given a Go+ file "main.gp":
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

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	out := Stack[U]{items: make([]U, 0, len(s.items))}
      	for _, x := range s.items {
      		out.items = append(out.items, f(x))
      	}
      	return out
      }

      func main() {
      	s := Stack[Option[int]]{items: []Option[int]{Some(1), None, Some(3)}}
      	total := 0
      	for _, n := range s.Map(func(o Option[int]) int { return o.UnwrapOr(0) }).items {
      		total += n
      	}
      	fmt.Println(total)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "4"
