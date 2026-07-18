Feature: Parsing pipelines and composition
  |> and >>> are adjacency-claimed token sequences (spec/grammar-v0.3.0.ebnf):
  lowest-precedence, left-associative expression operators. Placeholders
  need no grammar at all — `f(1, _)` already parses as Go.

  Scenario: A pipeline chain flattens into one expression
    Given a G++ file "p.gpp":
      """
      package p

      func f(xs []int) int {
      	return xs |> narrow |> total
      }
      """
    When I parse it
    Then parsing succeeds with 1 pipeline
    And pipeline 1 has head "xs" and stages "narrow | total"

  Scenario: Stage forms: calls, qualified names, placeholders, dot chains
    Given a G++ file "p.gpp":
      """
      package p

      import "strconv"

      func f(s Stack, lo, hi int) string {
      	return s |> Filter(isEven) |> clamp(lo, _, hi) |> strconv.Itoa |> .Map(double).Len()
      }
      """
    When I parse it
    Then parsing succeeds with 1 pipeline
    And pipeline 1 has head "s" and stages "Filter(isEven) | clamp(lo, _, hi) | strconv.Itoa | .Map(double).Len()"

  Scenario: Precedence — Go operators bind tighter; >>> binds tighter than |>
    Given a G++ file "p.gpp":
      """
      package p

      func f(a, b int) int {
      	x := a + b |> double
      	y := a |> double >>> negate
      	z := double >>> negate |> apply
      	_, _ = x, y
      	return z
      }
      """
    When I parse it
    Then parsing succeeds with 3 pipelines
    And parsing succeeds with 2 compositions
    And pipeline 1 has head "a + b" and stages "double"

  Scenario: Compositions flatten left-associatively
    Given a G++ file "p.gpp":
      """
      package p

      func f() {
      	g := parse >>> validate >>> save
      	_ = g
      }
      """
    When I parse it
    Then parsing succeeds with 1 composition
    And composition 1 has operands "parse | validate | save"

  Scenario: Pipelines nest inside stage arguments
    Given a G++ file "p.gpp":
      """
      package p

      func f(x, y int) int {
      	return x |> combine(y |> double)
      }
      """
    When I parse it
    Then parsing succeeds with 2 pipelines
    And pipeline 2 has head "y" and stages "double"

  Scenario: Pipelines work in control-flow headers and match arms
    Given a G++ file "p.gpp":
      """
      package p

      type Coin enum {
      	Heads
      	Tails
      }

      func f(c Coin, xs []int) int {
      	if xs |> valid {
      		match c {
      		case Heads:
      			return xs |> total
      		case Tails:
      		}
      	}
      	return 0
      }
      """
    When I parse it
    Then parsing succeeds with 2 pipelines
    And parsing succeeds with 1 match statement

  Scenario: A missing stage is a parse error
    Given a G++ file "p.gpp":
      """
      package p

      func f(x int) int {
      	return x |>
      }
      """
    When I parse it
    Then parsing fails with an error containing "expected operand"

  Scenario: A dot segment requires a name
    Given a G++ file "p.gpp":
      """
      package p

      func f(x int) int {
      	return x |> .
      }
      """
    When I parse it
    Then parsing fails with an error containing "expected method or field name"
