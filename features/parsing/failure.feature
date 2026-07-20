Feature: Parsing typed-failure syntax
  Postfix ? claims the scanner's illegal '?' only when written immediately
  after an expression; >=> is an adjacency-claimed token sequence; if,
  switch, and match are claimable at expression position
  (spec/grammar-v0.4.0.ebnf).

  Scenario: Postfix ? on calls, chains, and nested arguments
    Given a Go+ file "p.gp":
      """
      package p

      func f(path string) ([]byte, error) {
      	data := read(path)?
      	meta := parse(data)?.Refine()?
      	combine(read(path)?, meta)
      	return data, nil
      }
      """
    When I parse it
    Then parsing succeeds with 4 try suffixes

  Scenario: ? on pipeline stages and heads
    Given a Go+ file "p.gp":
      """
      package p

      func f(s string) int {
      	return start(s)? |> parse? |> count
      }
      """
    When I parse it
    Then parsing succeeds with 1 pipeline
    And parsing succeeds with 2 try suffixes

  Scenario: Expression if with else-if chains
    Given a Go+ file "p.gp":
      """
      package p

      func f(n int) int {
      	sign := if n < 0 { -1 } else if n == 0 { 0 } else { 1 }
      	return sign
      }
      """
    When I parse it
    Then parsing succeeds with 1 if expression

  Scenario: Expression switch, tagged and tagless
    Given a Go+ file "p.gp":
      """
      package p

      func f(score int) string {
      	grade := switch {
      	case score >= 90: "A"
      	case score >= 80: "B"
      	default: "C"
      	}
      	kind := switch score {
      	case 0, 100: "edge"
      	default: "mid"
      	}
      	return grade + kind
      }
      """
    When I parse it
    Then parsing succeeds with 2 switch expressions

  Scenario: Expression match with patterns and binders
    Given a Go+ file "p.gp":
      """
      package p

      func f(o Option) string {
      	label := match o {
      	case Some(v): describe(v)
      	case c := None: fallbackFor(c)
      	}
      	return label
      }
      """
    When I parse it
    Then parsing succeeds with 1 match expression

  Scenario: Expression forms nest and take suffixes
    Given a Go+ file "p.gp":
      """
      package p

      func f(c bool, o Option) int {
      	x := if c { match o { case Some(v): v case _: 0 } } else { fetch()? }
      	return x
      }
      """
    When I parse it
    Then parsing succeeds with 1 if expression
    And parsing succeeds with 1 match expression
    And parsing succeeds with 1 try suffix

  Scenario: A missing else is an error
    Given a Go+ file "p.gp":
      """
      package p

      func f(c bool) int {
      	x := if c { 1 }
      	return x
      }
      """
    When I parse it
    Then parsing fails with an error containing "missing else in if expression"

  Scenario: Kleisli chains flatten with per-link operators
    Given a Go+ file "p.gp":
      """
      package p

      func f() {
      	g := parse >=> validate >>> describe
      	_ = g
      }
      """
    When I parse it
    Then parsing succeeds with 1 composition
    And composition 1 has operands "parse | validate | describe"
