Feature: Parsing match statements
  A contextual `match` at statement position introduces exhaustive pattern
  matching: constructor patterns with nesting, wildcards, and whole-value
  binders. `match` remains an ordinary identifier everywhere else.

  Scenario: A basic match with constructor, bare, and wildcard arms
    Given a Go+ file "m.gp":
      """
      package m

      func area(s Shape) (a float64) {
      	match s {
      	case Circle(r):
      		a = 3 * r
      	case Point:
      		a = 0
      	case _:
      		a = -1
      	}
      	return
      }
      """
    When I parse it
    Then parsing succeeds with 1 match statement
    And match 1 has subject "s"
    And match 1 case 1 is "Circle(r)"
    And match 1 case 2 is "Point"
    And match 1 case 3 is "_"

  Scenario: Nested patterns, per-field wildcards, and binders
    Given a Go+ file "m.gp":
      """
      package m

      func eval(e Expr) int {
      	match e {
      	case Add(Lit(a), Lit(b)):
      		return a + b
      	case Add(l, _):
      		return eval(l)
      	case c := Lit(v):
      		_ = c
      		return v
      	}
      	return 0
      }
      """
    When I parse it
    Then parsing succeeds with 1 match statement
    And match 1 case 1 is "Add(Lit(a), Lit(b))"
    And match 1 case 2 is "Add(l, _)"
    And match 1 case 3 is "c := Lit(v)"

  Scenario: Qualified constructor patterns
    Given a Go+ file "m.gp":
      """
      package m

      import "example.com/dep/opt"

      func f(o opt.Option[int]) {
      	match o {
      	case opt.Some(v):
      		_ = v
      	case opt.None:
      	}
      }
      """
    When I parse it
    Then parsing succeeds with 1 match statement
    And match 1 case 1 is "opt.Some(v)"

  Scenario: Matches nest inside arm bodies, recorded pre-order
    Given a Go+ file "m.gp":
      """
      package m

      func f(a, b Shape) {
      	match a {
      	case Point:
      		match b {
      		case Point:
      		case _:
      		}
      	case _:
      	}
      }
      """
    When I parse it
    Then parsing succeeds with 2 match statements
    And match 1 has subject "a"
    And match 2 has subject "b"

  Scenario: Complex subjects parse like switch tags
    Given a Go+ file "m.gp":
      """
      package m

      func f(s Store) {
      	match s.load() {
      	case Point:
      	case _:
      	}
      	x := 1
      	match x + 1 {
      	case _:
      	}
      }
      """
    When I parse it
    Then parsing succeeds with 2 match statements
    And match 1 has subject "s.load()"
    And match 2 has subject "x + 1"

  Scenario: default is rejected inside match
    Given a Go+ file "m.gp":
      """
      package m

      func f(s Shape) {
      	match s {
      	case Point:
      	default:
      	}
      }
      """
    When I parse it
    Then parsing fails with an error containing "match statements do not have a default case; use 'case _:'"

  Scenario: Binders may not appear inside argument patterns
    Given a Go+ file "m.gp":
      """
      package m

      func f(e Expr) {
      	match e {
      	case Add(x := Lit(1), _):
      	}
      }
      """
    When I parse it
    Then parsing fails with an error containing "binder patterns may only appear at the top of a case"

  Scenario: A wildcard cannot be bound
    Given a Go+ file "m.gp":
      """
      package m

      func f(s Shape) {
      	match s {
      	case c := _:
      		_ = c
      	}
      }
      """
    When I parse it
    Then parsing fails with an error containing "cannot bind a wildcard pattern"
