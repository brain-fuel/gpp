Feature: Streaming input
  Parsers consume io.Readers incrementally: the buffer retains only
  what a live Try could rewind to, and a byte-at-a-time reader parses
  identically to a string — split UTF-8 runes included.

  Background:
    Given a module "example.com/demo" using the goplus standard library

  Scenario: A byte-at-a-time reader parses identically to a string
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"io"
      	"strconv"
      	"unicode"

      	"goforge.dev/goplus/std/parsec"
      )

      type trickle struct {
      	s string
      	i int
      }

      func (t *trickle) Read(p []byte) (int, error) {
      	if t.i >= len(t.s) {
      		return 0, io.EOF
      	}
      	p[0] = t.s[t.i]
      	t.i++
      	return 1, nil
      }

      func main() {
      	digits := parsec.Map(parsec.Many1(parsec.RuneWhen(unicode.IsDigit, "digit")), func(rs []rune) int {
      		n, _ := strconv.Atoi(string(rs))
      		return n
      	})
      	sum := parsec.Map(parsec.SepBy(parsec.Lexeme(digits), parsec.Symbol("+")), func(ns []int) int {
      		t := 0
      		for _, n := range ns {
      			t += n
      		}
      		return t
      	})
      	src := "1 + 2 + 3 + 4 — done"
      	a, _ := parsec.RunString(sum, src)
      	b, _ := parsec.Run(sum, &trickle{s: src})
      	fmt.Println(a, b, a == b)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "10 10 true"
