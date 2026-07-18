Feature: Methods on enums
  Interfaces cannot carry method bodies, so every method on an enum — plain
  or generic — lowers to a package-level function exactly like a v0.1.0
  generic method, and G++ keeps method-call syntax. Pointer receivers are
  errors: the lowered receiver type is the sealed interface.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: A plain method on an enum lowers to a package function
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Size enum {
      	Small(n int)
      	Big(n int)
      }

      func (s Size) Doubled() int {
      	return 2
      }

      func main() {
      	var s Size = Small{N: 21}
      	fmt.Println(s.Doubled())
      	_ = s
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "2"
    And the file "main_gpp.go" contains:
      """
      //gpp:method (Size) Doubled
      func SizeDoubled(s Size) int {
      """
    And the file "main_gpp.go" contains:
      """
      fmt.Println(SizeDoubled(s))
      """

  Scenario: A generic method on a generic enum composes both machineries
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func (o Option[T]) Pair[U any](u U) (Option[T], U) {
      	return o, u
      }

      func main() {
      	var o Option[int] = Some[int]{Value: 41}
      	back, tag := o.Pair("x")
      	fmt.Println(tag, back == Some[int]{Value: 41})
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "x true"
    And the file "main_gpp.go" contains:
      """
      //gpp:method (Option[T]) Pair[U]
      func OptionPair[T any, U any](o Option[T], u U) (Option[T], U) {
      """
    And the file "main_gpp.go" contains:
      """
      back, tag := OptionPair(o, "x")
      """

  Scenario: A plain enum method works as a bare method value
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Size enum {
      	Small(n int)
      	Big(n int)
      }

      func (s Size) Tag() string {
      	return "sized"
      }

      func main() {
      	var s Size = Big{N: 9}
      	f := s.Tag
      	fmt.Println(f())
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "sized"

  Scenario: A pointer receiver on an enum is an error
    Given a G++ file "main.gpp":
      """
      package main

      type Size enum {
      	Small(n int)
      }

      func (s *Size) Reset() {
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "enum receiver must not be a pointer; Size is an interface after lowering"
