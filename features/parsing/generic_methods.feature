Feature: Parsing generic methods
  Go+ is a strict superset of Go. Its only v0.1.0 grammar extension is a type
  parameter list on method declarations (spec/grammar-v0.1.0.ebnf). The
  frontend recovers those type parameters with original source positions and
  reports every other syntax error exactly as Go would.

  Scenario: A method may introduce its own type parameters
    Given a Go+ file "stack.gp":
      """
      package stack

      type Stack[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	out := Stack[U]{}
      	for _, x := range s.items {
      		out.items = append(out.items, f(x))
      	}
      	return out
      }
      """
    When I parse it
    Then parsing succeeds with 1 generic method
    And generic method 1 is "(Stack[T]) Map[U]"

  Scenario: Constraint-rich method type parameters survive recovery
    Given a Go+ file "algo.gp":
      """
      package algo

      type Bag[T any] struct{ xs []T }

      func (b Bag[T]) Reduce[Acc any, N interface{ ~int | ~string }](zero Acc, f func(Acc, T, N) Acc) Acc {
      	var acc Acc = zero
      	return acc
      }
      """
    When I parse it
    Then parsing succeeds with 1 generic method
    And generic method 1 is "(Bag[T]) Reduce[Acc, N]"

  Scenario: Pointer receivers and multiple generic methods
    Given a Go+ file "multi.gp":
      """
      package multi

      type Box[T any] struct{ v T }

      func (b *Box[T]) Set[U any](u U)   {}
      func (b Box[T]) Get[V any]() *V    { return nil }
      func (b Box[T]) Plain() T          { return b.v }
      """
    When I parse it
    Then parsing succeeds with 2 generic methods
    And generic method 1 is "(*Box[T]) Set[U]"
    And generic method 2 is "(Box[T]) Get[V]"

  Scenario: A method on a non-generic receiver may still be generic
    Given a Go+ file "plainrecv.gp":
      """
      package plainrecv

      type Registry struct{ names []string }

      func (r Registry) Collect[U any](f func(string) U) []U { return nil }
      """
    When I parse it
    Then parsing succeeds with 1 generic method
    And generic method 1 is "(Registry) Collect[U]"

  Scenario: Plain Go is valid Go+ with no generic methods
    Given a Go+ file "plain.gp":
      """
      package plain

      import "fmt"

      // Greet says hello.
      func Greet(name string) string {
      	return fmt.Sprintf("hello, %s", name)
      }
      """
    When I parse it
    Then parsing succeeds with 0 generic methods

  Scenario: Genuine syntax errors are reported, not swallowed
    Given a Go+ file "broken.gp":
      """
      package broken

      func (s Stack[T]) Map[U any](f func(T) U Stack[U] {
      	return
      }
      """
    When I parse it
    Then parsing fails with an error containing "missing ',' in parameter list"
