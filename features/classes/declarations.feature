Feature: Class declarations lower to witness structs
  A class lowers to a flat witness struct whose fields are the operations
  (embeds stay as anonymous fields until resolution flattens them), law
  members to Law* methods with an implicit bool result, and default
  operation bodies to Default* pointer-receiver methods. Bodies keep their
  source bytes; //goplus:class, //goplus:law, and //goplus:default markers make the
  generated Go self-describing for cross-package use.

  Scenario: The witness shape
    Given a Go+ file "main.gp":
      """
      package main

      // Magma is a closed binary operation.
      type Magma[T any] class {
      	Combine(a, b T) T
      }

      type Monoid[T any] class {
      	Magma[T]
      	Empty() T
      	law LeftId(a T) { return Combine(Empty(), a) == a }
      }

      type Group[T any] class {
      	Monoid[T]
      	Invert(a T) T
      	LeftDiv(a, b T) T { return Combine(Invert(b), a) }
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 0
    And the file "main_gp.go" contains:
      """
      // Magma is a closed binary operation.
      //
      //goplus:class Magma[T any]
      type Magma[T any] struct {
      	Combine func(a, b T) T
      }
      """
    And the file "main_gp.go" contains:
      """
      //goplus:class Monoid[T any] embeds(Magma)
      type Monoid[T any] struct {
      	Magma[T]
      	Empty func() T
      }

      //goplus:law (Monoid[T]) LeftId(a T)
      func (m Monoid[T]) LawLeftId(a T) bool { return Combine(Empty(), a) == a }
      """
    And the file "main_gp.go" contains:
      """
      //goplus:class Group[T any] embeds(Monoid)
      type Group[T any] struct {
      	Monoid[T]
      	Invert  func(a T) T
      	LeftDiv func(a, b T) T
      }

      //goplus:default (Group[T]) LeftDiv(a, b T)
      func (m Group[T]) DefaultLeftDiv(a, b T) T { return Combine(Invert(b), a) }
      """

  Scenario: Generation is idempotent over classes
    Given a Go+ file "main.gp":
      """
      package main

      type Magma[T any] class {
      	Combine(a, b T) T
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 0
    And I record the generated files
    When I run goplus with arguments "gen ."
    Then the exit code is 0
    And the generated files are unchanged

  Scenario: A class needs exactly one type parameter
    Given a Go+ file "main.gp":
      """
      package main

      type Pair[A any, B any] class {
      	Combine(a A, b B) A
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "a class must have exactly one type parameter (v0.5.0); Pair has 2"

  Scenario: Duplicate members are rejected
    Given a Go+ file "main.gp":
      """
      package main

      type M[T any] class {
      	Combine(a, b T) T
      	Combine(a T) T
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "class M declares operation Combine twice"

  Scenario: A grouped type block cannot hold a class
    Given a Go+ file "main.gp":
      """
      package main

      type (
      	M[T any] class {
      		Combine(a, b T) T
      	}
      )
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "declare each class in its own type declaration"

  Scenario: An operation may declare multiple results
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """
    And a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Fetcher[T any] class {
      	Fetch(host T, key string) (string, error)
      }

      type memHost struct{ m map[string]string }

      instance Mem Fetcher[memHost] {
      	Fetch(host memHost, key string) (string, error) {
      		v, ok := host.m[key]
      		if !ok {
      			return "", fmt.Errorf("missing %s", key)
      		}
      		return v, nil
      	}
      }

      func lookup[T Fetcher](host T, key string) string {
      	v, err := Fetch(host, key)
      	if err != nil {
      		return "?"
      	}
      	return v
      }

      func main() {
      	h := memHost{m: map[string]string{"a": "1"}}
      	fmt.Println(lookup(h, "a"), lookup(h, "b"))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "1 ?"
