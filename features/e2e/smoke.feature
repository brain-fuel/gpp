Feature: End-to-end smoke
  One realistic module exercising the whole v0.1.0 surface: a library
  package authored in Go+, a Go+ consumer using chained calls, explicit
  instantiation, method values and promotion, a plain-Go consumer of the
  lowered API, tests, and a clean -check.

  Scenario: A full module builds, runs, tests, and stays fresh
    Given a file "go.mod":
      """
      module example.com/smoke

      go 1.24
      """
    And a Go+ file "collections/stack.gp":
      """
      package collections

      // Stack is a LIFO container.
      type Stack[T any] struct{ Items []T }

      // Map transforms every element.
      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	out := Stack[U]{Items: make([]U, 0, len(s.Items))}
      	for _, x := range s.Items {
      		out.Items = append(out.Items, f(x))
      	}
      	return out
      }

      // Push converts and appends.
      func (s *Stack[T]) Push[V any](v V, conv func(V) T) {
      	s.Items = append(s.Items, conv(v))
      }

      // Len is a plain method; it stays a method.
      func (s Stack[T]) Len() int { return len(s.Items) }
      """
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      	"strings"

      	"example.com/smoke/collections"
      )

      type App struct {
      	collections.Stack[int]
      }

      func main() {
      	app := App{}
      	app.Push("40", func(s string) int { n, _ := strconv.Atoi(s); return n + 2 })

      	upper := app.Map(strconv.Itoa).Map(strings.ToUpper)
      	fmt.Println("chained:", upper.Items, "len:", app.Len())

      	mapper := app.Stack.Map[string]
      	fmt.Println("value:", mapper(func(x int) string { return strconv.Itoa(x * 2) }).Items)

      	empty := app.Stack.Map[string](strconv.Itoa)
      	fmt.Println("explicit:", empty.Items)
      }
      """
    And a file "collections/plainuse.go":
      """
      package collections

      import "strconv"

      // PlainGoUse proves the lowered API is ordinary Go.
      func PlainGoUse() []string {
      	s := Stack[int]{Items: []int{7}}
      	return Map(s, strconv.Itoa).Items
      }
      """
    And a file "collections/stack_test.go":
      """
      package collections

      import "testing"

      func TestPlainGoUse(t *testing.T) {
      	if got := PlainGoUse(); len(got) != 1 || got[0] != "7" {
      		t.Fatalf("got %v", got)
      	}
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "chained: [42] len: 1"
    And stdout contains "value: [84]"
    And stdout contains "explicit: [42]"
    When I run goplus with arguments "test ./..."
    Then the exit code is 0
    And running goplus with arguments "gen -check ./..." exits with 0
    And running goplus with arguments "vet ./..." exits with 0
