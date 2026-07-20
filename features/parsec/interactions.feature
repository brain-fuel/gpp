Feature: parsec interoperates with the rest of the language
  Run's (T, error) output rides the railway; the derived ReplyCases
  fold consumes replies without a match; parsers cross packages like
  any generated Go.

  Background:
    Given a module "example.com/demo" using the goplus standard library

  Scenario: Run output through the railway, Reply through its fold
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      	"strings"
      	"unicode"

      	"goforge.dev/goplus/std/parsec"
      	"goforge.dev/goplus/std/result"
      )

      func number() parsec.Parser[int] {
      	return parsec.Map(parsec.Many1(parsec.RuneWhen(unicode.IsDigit, "digit")), func(rs []rune) int {
      		n, _ := strconv.Atoi(string(rs))
      		return n
      	})
      }

      func parseInt(s string) result.Result[int, error] {
      	return result.Of(parsec.RunString(number(), s))
      }

      func main() {
      	doubled := "21" |> parseInt |> func(n int) int { return n * 2 } |> .UnwrapOr(-1)
      	fmt.Println(doubled)

      	bad := "x" |> parseInt |> .UnwrapOr(-1)
      	fmt.Println(bad)
      	fmt.Println(result.Of(5, nil) |> .UnwrapOr(0))

      	rep := number()(parsec.StartInput(parsec.NewStream(strings.NewReader("7!"))))
      	desc := parsec.Fold(rep, parsec.ReplyCases[int, string]{
      		ConsumedOk:  func(v int, rest parsec.Input) string { return "ok " + strconv.Itoa(v) },
      		EmptyOk:     func(v int, rest parsec.Input) string { return "empty ok" },
      		ConsumedErr: func(e parsec.ParseError) string { return "consumed err" },
      		EmptyErr:    func(e parsec.ParseError) string { return "empty err" },
      	})
      	fmt.Println(desc)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      42
      -1
      5
      ok 7
      """
