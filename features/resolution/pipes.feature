Feature: Pipeline resolution
  x |> seg inserts the piped value as the first argument (or at the
  placeholder slot). Bare names resolve against the piped value's members
  — full Go selector semantics plus goplus methods — and against functions,
  constructors, builtins, and conversions in scope; resolving to both is a
  hard error with two explicit spellings. Multi-result stages follow Go's
  spread rule.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Function segments insert first-arg; placeholders choose the slot
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func double(n int) int { return n * 2 }

      func clamp(lo, n, hi int) int {
      	if n < lo {
      		return lo
      	}
      	if n > hi {
      		return hi
      	}
      	return n
      }

      func add(a, b int) int { return a + b }

      func main() {
      	fmt.Println(5 |> double |> add(1) |> clamp(0, _, 10))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "10"
    And the file "main_gp.go" contains:
      """
      fmt.Println(clamp(0, add(double(5), 1), 10))
      """

  Scenario: Bare segments resolve to goplus methods, promoted members, and functions
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	out := Stack[U]{items: make([]U, 0, len(s.items))}
      	for _, x := range s.items {
      		out.items = append(out.items, f(x))
      	}
      	return out
      }

      func (s Stack[T]) Total(sum func(T, T) T, zero T) T {
      	acc := zero
      	for _, x := range s.items {
      		acc = sum(acc, x)
      	}
      	return acc
      }

      func addInts(a, b int) int { return a + b }

      func main() {
      	s := Stack[int]{items: []int{1, 2, 3}}
      	got := s |> Map(func(n int) int { return n * n }) |> Total(addInts, 0)
      	fmt.Println(got)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "14"

  Scenario: Dot segments force members, including chains and enum methods
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

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

      func (o Option[T]) UnwrapOr(fb T) T {
      	match o {
      	case Some(v):
      		return v
      	case None:
      		return fb
      	}
      }

      func double(n int) int { return n * 2 }

      func main() {
      	got := 21 |> Some |> .Map(double).UnwrapOr(0)
      	fmt.Println(got)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "42"

  Scenario: Builtins, conversions, and qualified functions pipe as functions
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strings"
      )

      type Celsius float64

      func main() {
      	n := []int{1, 2, 3} |> len
      	c := 21.5 |> Celsius
      	s := "hello world" |> strings.ToUpper
      	fmt.Println(n, c, s)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "3 21.5 HELLO WORLD"

  Scenario: A member/function collision is a hard error with both spellings
    Given a Go+ file "main.gp":
      """
      package main

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	return Stack[U]{}
      }

      func Map(s Stack[int], f func(int) int) Stack[int] {
      	return s
      }

      func double(n int) int { return n * 2 }

      func main() {
      	s := Stack[int]{}
      	_ = s |> Map(double)
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "Map is both a method of Stack[int] and a function in this package; write .Map(double) for the method or Map(_, double) for the function"

  Scenario: The explicit spellings resolve the collision both ways
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Size[U any]() int {
      	return len(s.items)
      }

      func Size(s Stack[int]) int {
      	return -1
      }

      func main() {
      	s := Stack[int]{items: []int{1, 2}}
      	fmt.Println(s |> .Size[string]())
      	fmt.Println(s |> Size(_))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "2"
    And stdout contains "-1"

  Scenario: Multi-result stages spread into an exactly matching segment
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      func describe(n int, err error) string {
      	if err != nil {
      		return "bad"
      	}
      	return "ok " + strconv.Itoa(n)
      }

      func main() {
      	fmt.Println("42" |> strconv.Atoi |> describe)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "ok 42"

  Scenario: A spread mismatch is a branded error
    Given a Go+ file "main.gp":
      """
      package main

      import "strconv"

      func double(n int) int { return n * 2 }

      func main() {
      	_ = "42" |> strconv.Atoi |> double
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot pipe the 2 results of strconv.Atoi"
    And stderr contains "into double (want int)"

  Scenario: Neither member nor function is a definitive error
    Given a Go+ file "main.gp":
      """
      package main

      func main() {
      	x := 5
      	_ = x |> Nonesuch
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "Nonesuch is neither a method of int nor a function in scope"

  Scenario: A boolean stage gets the parenthesize hint
    Given a Go+ file "main.gp":
      """
      package main

      func valid(xs []int) bool { return len(xs) > 0 }

      func main() {
      	xs := []int{1}
      	_ = xs |> len > 0
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "parenthesize the pipeline: (x |> f) > "
