Feature: Promotion through embedded fields
  Generic methods promote through embedded fields exactly like Go methods:
  breadth-first, shallowest depth wins, same-depth duplicates are ambiguous.
  The rewrite selects the embedded field explicitly.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: A generic method promoted from an embedded value field
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

      type Widget struct {
      	Stack[int]
      	name string
      }

      func main() {
      	w := Widget{Stack: Stack[int]{items: []int{3, 4}}, name: "w"}
      	fmt.Println(w.Map(strconv.Itoa).items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[3 4]"
    And the file "main_gp.go" contains:
      """
      fmt.Println(Map(w.Stack, strconv.Itoa).items)
      """

  Scenario: A pointer-receiver method promoted through a pointer embedded field
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Stack[T any] struct{ items []T }

      func (s *Stack[T]) Push[V any](v V, conv func(V) T) {
      	s.items = append(s.items, conv(v))
      }

      type Widget struct {
      	*Stack[string]
      }

      func main() {
      	w := Widget{Stack: &Stack[string]{}}
      	w.Push(7, func(v int) string { return fmt.Sprint(v) })
      	fmt.Println(w.Stack.items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[7]"
    And the file "main_gp.go" contains:
      """
      Push(w.Stack, 7, func(v int) string { return fmt.Sprint(v) })
      """

  Scenario: Deeper nesting still resolves, shallowest first
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Inner[T any] struct{ v T }

      func (i Inner[T]) Get[U any](f func(T) U) U {
      	return f(i.v)
      }

      type Middle struct{ Inner[int] }
      type Outer struct{ Middle }

      func main() {
      	o := Outer{Middle{Inner[int]{v: 21}}}
      	fmt.Println(o.Get(func(x int) int { return x * 2 }))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "42"
    And the file "main_gp.go" contains:
      """
      fmt.Println(Get(o.Middle.Inner, func(x int) int { return x * 2 }))
      """

  Scenario: The same generic method at the same depth is ambiguous
    Given a Go+ file "main.gp":
      """
      package main

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	return Stack[U]{}
      }

      type A struct{ Stack[int] }
      type B struct{ Stack[int] }
      type Both struct {
      	A
      	B
      }

      func main() {
      	var x Both
      	x.Map(func(v int) int { return v })
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 2
    And stderr contains "ambiguous generic method Map"
