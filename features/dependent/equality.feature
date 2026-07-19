Feature: Propositional equality
  Eq[a, b] is a proposition: a proof parameter (always quantity 0)
  discharged at call sites by `refl` through the arithmetic decider,
  with the callee's other index parameters bound to the caller's
  arguments. Everything erases — Eq, refl, and the parameters carrying
  them leave no trace in the generated Go. An equality the decider
  cannot prove is an error naming both sides after substitution.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: refl discharges ground and symbolic equalities
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Vec[T any, n nat] enum {
      	Nil() Vec[T, 0]
      	Cons(head T, tail Vec[T, n]) Vec[T, n+1]
      }

      func Cast[T any](0 n nat, 0 m nat, 0 p Eq[n, m], v Vec[T, n]) Vec[T, m] {
      	return v
      }

      func Swap(0 n nat, 0 m nat, 0 p Eq[n+m, m+n]) string {
      	return "commutes"
      }

      func main() {
      	v := Cons(1, Cons(2, Nil[int]()))
      	w := Cast(1+1, 2, refl, v)
      	_ = w
      	fmt.Println("cast ok")
      	fmt.Println(Swap(3, 4, refl))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      cast ok
      commutes
      """
    And the file "main_gpp.go" contains:
      """
      func Cast[T any](v Vec[T]) Vec[T] {
      """
    And the file "main_gpp.go" contains:
      """
      	w := Cast(v)
      """
    And the file "main_gpp.go" contains:
      """
      	fmt.Println(Swap())
      """

  Scenario: An unprovable equality is an error naming both sides
    Given a G++ file "main.gpp":
      """
      package main

      type Vec[T any, n nat] enum {
      	Nil() Vec[T, 0]
      	Cons(head T, tail Vec[T, n]) Vec[T, n+1]
      }

      func Cast[T any](0 n nat, 0 m nat, 0 p Eq[n, m], v Vec[T, n]) Vec[T, m] {
      	return v
      }

      func main() {
      	v := Cons(1, Nil[int]())
      	_ = Cast(1, 2, refl, v)
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "cannot prove 1 = 2 at this call to Cast; the arithmetic decider could not discharge refl"

  Scenario: A proof argument must be refl
    Given a G++ file "main.gpp":
      """
      package main

      func Claim(0 n nat, 0 p Eq[n, n]) string {
      	return "ok"
      }

      func main() {
      	x := 1
      	_ = Claim(1, x)
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "the proof argument for p of Claim must be refl in v0.7.0"

  Scenario: A proof parameter must be erased
    Given a G++ file "main.gpp":
      """
      package main

      func Bad(0 n nat, p Eq[n, n]) string {
      	return "no"
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "a proof parameter (Eq[n, n]) must be erased: give p quantity 0"
