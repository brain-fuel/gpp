Feature: Generic method values
  An instantiated generic method value (s.Map[string]) lowers to a closure
  over the lowered function, capturing the receiver at bind time — the same
  semantics Go gives ordinary method values. Uninstantiated generic method
  values are errors, matching Go's rule for generic function values.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Binding and reusing an instantiated method value
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	out := Stack[U]{items: make([]U, 0, len(s.items))}
      	for _, x := range s.items {
      		out.items = append(out.items, f(x))
      	}
      	return out
      }

      func main() {
      	s := Stack[int]{items: []int{5, 6}}
      	mapper := s.Map[string]
      	a := mapper(strconv.Itoa)
      	b := mapper(func(x int) string { return strconv.Itoa(x * 10) })
      	fmt.Println(a.items, b.items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[5 6] [50 60]"

  Scenario: The receiver is captured at bind time, like a Go method value
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Counter[T any] struct{ n int }

      func (c Counter[T]) Report[U any](u U) (int, U) {
      	return c.n, u
      }

      func main() {
      	c := Counter[string]{n: 1}
      	report := c.Report[string]
      	c.n = 99
      	got, tag := report("early")
      	fmt.Println(got, tag)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "1 early"

  Scenario: A variadic generic method survives as a method value
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Bag[T any] struct{ items []T }

      func (b Bag[T]) With[U any](tag U, more ...T) Bag[T] {
      	return Bag[T]{items: append(append([]T{}, b.items...), more...)}
      }

      func main() {
      	b := Bag[int]{items: []int{1}}
      	with := b.With[string]
      	fmt.Println(with("x", 2, 3).items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[1 2 3]"

  Scenario: An uninstantiated generic method value is an error
    Given a Go+ file "main.gp":
      """
      package main

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	return Stack[U]{}
      }

      func main() {
      	s := Stack[int]{}
      	_ = s.Map
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 2
    And stderr contains "without instantiation"
