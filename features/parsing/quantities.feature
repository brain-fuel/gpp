Feature: Quantity prefixes and total functions parse and strip
  v0.7.0 frontend: QTT quantity prefixes on parameters (`0 n int`
  erased, `1 f *os.File` linear, `m x T` multiplicity variable) and
  `total func` declarations are strict-superset claims — every claimed
  form is invalid Go, and every neighboring valid-Go form keeps its Go
  meaning. Pass 1 strips both spellings from the generated Go; the
  dependent core's checking arrives in later phases.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Quantities and total strip; the program still runs
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      total func Twice(a int) int {
      	return a + a
      }

      func join(0 n int, x string, 1 s string) string {
      	_ = n
      	return x + s
      }

      func through(q f func() int) int {
      	return f()
      }

      func main() {
      	fmt.Println(Twice(21))
      	fmt.Println(join(3, "a", "b"))
      	fmt.Println(through(func() int { return 9 }))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      42
      ab
      9
      """
    And the file "main_gpp.go" contains:
      """
      func Twice(a int) int {
      """
    And the file "main_gpp.go" contains:
      """
      func join(n int, x string, s string) string {
      """
    And the file "main_gpp.go" contains:
      """
      func through(f func() int) int {
      """

  Scenario: A quantity variadic parameter strips
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      func sum(1 xs ...int) int {
      	t := 0
      	for _, x := range xs {
      		t += x
      	}
      	return t
      }

      func main() {
      	fmt.Println(sum(1, 2, 3))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "6"
    And the file "main_gpp.go" contains:
      """
      func sum(xs ...int) int {
      """

  Scenario: Valid Go parameter forms keep their Go meaning
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type b = string
      type d = int

      func pair(a b, c d) string {
      	_ = c
      	return a
      }

      func poly[T any](m string, v T) T {
      	_ = m
      	return v
      }

      func main() {
      	total := 5
      	total++
      	fmt.Println(pair("x", 1), poly("q", total))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "x 6"
    And the file "main_gpp.go" contains:
      """
      func pair(a b, c d) string {
      """
    And the file "main_gpp.go" contains:
      """
      func poly[T any](m string, v T) T {
      """

  Scenario: Only 0 and 1 are quantity literals
    Given a G++ file "main.gpp":
      """
      package main

      func f(2 n int) int {
      	return n
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "expected ')'"

  Scenario: A quantity requires a named parameter
    Given a G++ file "main.gpp":
      """
      package main

      func f(0 int) int {
      	return 0
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "a quantity annotation requires a named parameter with a type"
