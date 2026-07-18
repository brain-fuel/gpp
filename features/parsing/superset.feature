Feature: Strict superset — enum and match remain ordinary identifiers
  Every valid Go program is a valid G++ program. The contextual keywords
  claim only token sequences that are invalid Go; each scenario here is a
  valid Go form that must keep its Go meaning, parsing with zero enums and
  zero match statements.

  Scenario: match as a variable
    Given a G++ file "s.gpp":
      """
      package s

      func f() int {
      	match := 5
      	match++
      	match = match + 1
      	return match
      }
      """
    When I parse it
    Then parsing succeeds with 0 match statements

  Scenario: match as a function, call syntax
    Given a G++ file "s.gpp":
      """
      package s

      func match(x int) int { return x }

      func f() int {
      	return match(3)
      }
      """
    When I parse it
    Then parsing succeeds with 0 match statements

  Scenario: match as a type in composite literals and indexing
    Given a G++ file "s.gpp":
      """
      package s

      type match struct{ n int }

      func f() int {
      	m := match{n: 1}
      	xs := []int{7}
      	match := xs
      	match[0] = 2
      	return m.n + match[0]
      }
      """
    When I parse it
    Then parsing succeeds with 0 match statements

  Scenario: match as a channel and a label
    Given a G++ file "s.gpp":
      """
      package s

      func f(match chan int) {
      	match <- 1
      match:
      	for {
      		break match
      	}
      }
      """
    When I parse it
    Then parsing succeeds with 0 match statements

  Scenario: match as a selector base
    Given a G++ file "s.gpp":
      """
      package s

      type t struct{ f int }

      func g() int {
      	var match t
      	return match.f
      }
      """
    When I parse it
    Then parsing succeeds with 0 match statements

  Scenario: enum as a type name
    Given a G++ file "s.gpp":
      """
      package s

      type enum int

      type X enum

      var enum2 enum = 3

      func f(e enum) enum { return e }
      """
    When I parse it
    Then parsing succeeds with 0 enums

  Scenario: Spaced near-misses of |> and >>> stay ordinary Go
    Given a G++ file "s.gpp":
      """
      package s

      func f(a, b, c int) bool {
      	x := (a | b) > c
      	y := a | b
      	z := a >> b
      	w := a >> b >> c
      	_, _, _ = y, z, w
      	return x
      }
      """
    When I parse it
    Then parsing succeeds with 0 pipelines
    And parsing succeeds with 0 compositions

  Scenario: Blank identifiers in calls parse as plain Go
    Given a G++ file "s.gpp":
      """
      package s

      func g(x any) {}

      func f() {
      	g(nil)
      	_ = 1
      	for _ = range []int{1} {
      	}
      }
      """
    When I parse it
    Then parsing succeeds with 0 pipelines

  Scenario: enum and match as parameters and struct fields
    Given a G++ file "s.gpp":
      """
      package s

      type config struct {
      	enum  string
      	match int
      }

      func f(enum, match int) int { return enum + match }
      """
    When I parse it
    Then parsing succeeds with 0 enums
    And parsing succeeds with 0 match statements
