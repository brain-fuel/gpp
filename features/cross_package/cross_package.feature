Feature: Cross-package generic methods
  The emitted Go is the single distribution artifact: //goplus:method markers
  make it self-describing, so importing packages get method syntax even when
  the dependency ships only its generated Go — no .gp sources, no Go+
  toolchain.

  Scenario: Method syntax across packages in the same module
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """
    And a Go+ file "lib/stack.gp":
      """
      package lib

      type Stack[T any] struct{ Items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	out := Stack[U]{Items: make([]U, 0, len(s.Items))}
      	for _, x := range s.Items {
      		out.Items = append(out.Items, f(x))
      	}
      	return out
      }
      """
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"example.com/demo/lib"
      )

      func main() {
      	s := lib.Stack[int]{Items: []int{9, 10}}
      	fmt.Println(s.Map(strconv.Itoa).Items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[9 10]"
    And the file "main_gp.go" contains:
      """
      fmt.Println(lib.Map(s, strconv.Itoa).Items)
      """

  Scenario: A distributed dependency works without its .gp sources
    Given a file "dep/go.mod":
      """
      module example.com/dep

      go 1.24
      """
    And a Go+ file "dep/lib/stack.gp":
      """
      package lib

      type Stack[T any] struct{ Items []T }

      func (s *Stack[T]) Push[V any](v V, conv func(V) T) {
      	s.Items = append(s.Items, conv(v))
      }
      """
    And I run goplus in "dep" with arguments "gen ./..."
    And the file "dep/lib/stack_gp.go" contains:
      """
      //goplus:method (*Stack[T]) Push[V]
      """
    And the file "dep/lib/stack.gp" is deleted
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
      	var s lib.Stack[string]
      	s.Push(3, func(v int) string { return fmt.Sprint(v * 111) })
      	fmt.Println(s.Items)
      }
      """
    When I run goplus in "app" with arguments "run ."
    Then the exit code is 0
    And stdout contains "[333]"
    And the file "app/main_gp.go" contains:
      """
      lib.Push(&s, 3, func(v int) string { return fmt.Sprint(v * 111) })
      """

  Scenario: Plain-Go consumers call the lowered function directly
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """
    And a Go+ file "lib/stack.gp":
      """
      package lib

      type Stack[T any] struct{ Items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	out := Stack[U]{Items: make([]U, 0, len(s.Items))}
      	for _, x := range s.Items {
      		out.Items = append(out.Items, f(x))
      	}
      	return out
      }
      """
    And a file "main.go":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"example.com/demo/lib"
      )

      func main() {
      	s := lib.Stack[int]{Items: []int{5}}
      	fmt.Println(lib.Map(s, strconv.Itoa).Items)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "[5]"

  Scenario: Classes, instances, and constrained callers span packages
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """
    And a Go+ file "algebra/algebra.gp":
      """
      package algebra

      type Monoid[T any] class {
      	Combine(a, b T) T
      	Empty() T
      }

      func Accumulate[T Monoid](xs []T) T {
      	acc := Empty()
      	for _, x := range xs {
      		acc = Combine(acc, x)
      	}
      	return acc
      }
      """
    And a Go+ file "nums/nums.gp":
      """
      package nums

      import "example.com/demo/algebra"

      instance IntAdd algebra.Monoid[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      }
      """
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"example.com/demo/algebra"
      	"example.com/demo/nums"
      )

      var _ = nums.IntAdd

      func main() {
      	fmt.Println(algebra.Accumulate([]int{1, 2, 3, 4}))
      	fmt.Println(algebra.Accumulate(nums.IntAdd, []int{5, 6}))
      }
      """
    When I run goplus with arguments "gen ./..."
    Then the exit code is 0
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      10
      11
      """
