Feature: parsec core combinators
  goforge.dev/gpp/std/parsec is a parser-combinator library with
  parsec-style consumed/empty semantics over streaming input: Or
  commits once a branch has consumed input; Try restores the lookahead.
  The Reply type is a gpp enum, matched by the library and by user
  code. Errors carry line:col positions and Label'd expectations.

  Background:
    Given a module "example.com/demo" using the gpp standard library

  Scenario: Or commits on consumption; Try restores the lookahead
    Given a G++ file "main.gpp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/gpp/std/parsec"
      )

      func main() {
      	committed := parsec.Or(parsec.Str("ab"), parsec.Str("ac"))
      	_, err := parsec.RunString(committed, "ac")
      	fmt.Println("committed fails:", err != nil)

      	restored := parsec.Or(parsec.Try(parsec.Str("ab")), parsec.Str("ac"))
      	v, err2 := parsec.RunString(restored, "ac")
      	fmt.Println("restored:", v, err2 == nil)
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      committed fails: true
      restored: ac true
      """

  Scenario: Errors carry positions and labels; user code matches Reply
    Given a G++ file "main.gpp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/gpp/std/parsec"
      )

      func main() {
      	p := parsec.Bind(parsec.Str("a\nb"), func(_ string) parsec.Parser[rune] {
      		return parsec.Label(parsec.Rune('x'), "the letter x")
      	})
      	_, err := parsec.RunString(p, "a\nbz")
      	fmt.Println(err)

      	rep := parsec.Rune('q')(parsec.StartInput(parsec.NewStream(nil)))

      	match rep {
      	case parsec.ConsumedOk(v, rest):
      		_ = rest
      		fmt.Println("ok", v)
      	case parsec.EmptyErr(e):
      		fmt.Println("empty error at", e.Line, e.Col)
      	case _:
      		fmt.Println("other")
      	}
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      2:2: unexpected 'z', expecting the letter x
      empty error at 1 1
      """
