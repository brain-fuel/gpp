Feature: Resolving generic method calls
  Go+ callers use method syntax; the generator rewrites each call to the
  lowered package-level function, letting Go's own type inference type the
  call. Receiver auto-& and auto-* follow Go's method call rules exactly.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: A basic generic method call with inference
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
      	s := Stack[int]{items: []int{1, 2, 3}}
      	t := s.Map(strconv.Itoa)
      	fmt.Println(t.items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[1 2 3]"
    And the file "main_gp.go" contains:
      """
      t := Map(s, strconv.Itoa)
      """

  Scenario: Chained calls resolve inside-out across fixpoint iterations
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      	"strings"
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
      	s := Stack[int]{items: []int{7, 8}}
      	r := s.Map(strconv.Itoa).Map(func(x string) string { return strings.Repeat(x, 2) })
      	fmt.Println(r.items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[77 88]"
    And the file "main_gp.go" contains:
      """
      r := Map(Map(s, strconv.Itoa), func(x string) string { return strings.Repeat(x, 2) })
      """

  Scenario: Explicit instantiation gains the receiver's type arguments as prefix
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Empty[U any]() Stack[U] {
      	return Stack[U]{}
      }

      func main() {
      	s := Stack[int]{items: []int{1}}
      	e := s.Empty[string]()
      	e.items = append(e.items, "ok")
      	fmt.Println(e.items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[ok]"
    And the file "main_gp.go" contains:
      """
      e := Empty[int, string](s)
      """

  Scenario: Calling a pointer-receiver method on an addressable value takes its address
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Stack[T any] struct{ items []T }

      func (s *Stack[T]) Push[V any](v V, conv func(V) T) {
      	s.items = append(s.items, conv(v))
      }

      func main() {
      	var s Stack[string]
      	s.Push(42, func(v int) string { return fmt.Sprint(v) })
      	fmt.Println(s.items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[42]"
    And the file "main_gp.go" contains:
      """
      Push(&s, 42, func(v int) string { return fmt.Sprint(v) })
      """

  Scenario: Calling a value-receiver method through a pointer dereferences it
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Len[U any]() int {
      	return len(s.items)
      }

      func main() {
      	s := &Stack[int]{items: []int{1, 2}}
      	fmt.Println(s.Len[string]())
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "2"
    And the file "main_gp.go" contains:
      """
      Len[int, string](*s)
      """

  Scenario: A real Go method with the same name always wins
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	return Stack[U]{}
      }

      type Widget struct{}

      func (w Widget) Map(f func(int) int) string {
      	return "the real Map"
      }

      func main() {
      	var w Widget
      	fmt.Println(w.Map(func(x int) int { return x }))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "the real Map"
    And the file "main_gp.go" contains:
      """
      fmt.Println(w.Map(func(x int) int { return x }))
      """

  Scenario: Calling a pointer-receiver method on a non-addressable value is an error
    Given a Go+ file "main.gp":
      """
      package main

      type Stack[T any] struct{ items []T }

      func (s *Stack[T]) Push[V any](v V, conv func(V) T) {
      	s.items = append(s.items, conv(v))
      }

      func mk() Stack[int] { return Stack[int]{} }

      func main() {
      	mk().Push("x", func(s string) int { return len(s) })
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 2
    And stderr contains "cannot call pointer method Push"
