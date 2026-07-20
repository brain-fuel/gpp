Feature: An expression evaluator in twenty lines
  The showcase: a full arithmetic grammar — precedence, associativity,
  parentheses, whitespace — from Chainl1, Between, and Defer, composed
  with goplus pipelines. This is the README example.

  Background:
    Given a module "example.com/demo" using the goplus standard library

  Scenario: Arithmetic with precedence, parens, and errors
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      	"unicode"

      	"goforge.dev/goplus/std/parsec"
      )

      func number() parsec.Parser[int] {
      	digits := parsec.Many1(parsec.RuneWhen(unicode.IsDigit, "digit"))
      	toInt := func(rs []rune) int { n, _ := strconv.Atoi(string(rs)); return n }
      	return parsec.Label(parsec.Lexeme(parsec.Map(digits, toInt)), "number")
      }

      func op(sym string, f func(int, int) int) parsec.Parser[func(int, int) int] {
      	return parsec.Map(parsec.Symbol(sym), func(string) func(int, int) int { return f })
      }

      func grammar() parsec.Parser[int] {
      	var expr parsec.Parser[int]
      	factor := parsec.Label(parsec.Or(number(), parsec.Between(parsec.Symbol("("), parsec.Defer(&expr), parsec.Symbol(")"))), "expression")
      	term := parsec.Chainl1(factor, parsec.Or(op("*", func(a, b int) int { return a * b }), op("/", func(a, b int) int { return a / b })))
      	expr = parsec.Chainl1(term, parsec.Or(op("+", func(a, b int) int { return a + b }), op("-", func(a, b int) int { return a - b })))
      	return parsec.Then(parsec.Spaces(), parsec.Before(expr, parsec.EOF()))
      }

      func eval(src string) string {
      	v, err := parsec.RunString(grammar(), src)
      	if err != nil {
      		return err.Error()
      	}
      	return strconv.Itoa(v)
      }

      func main() {
      	fmt.Println("1+2*3" |> eval)
      	fmt.Println("(1+2)*3" |> eval)
      	fmt.Println(" 10 - 4 - 3 " |> eval)
      	fmt.Println("1+*2" |> eval)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      7
      9
      3
      1:3: unexpected '*', expecting expression
      """
