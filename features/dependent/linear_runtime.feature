Feature: Linear runtime cells
  A linear (quantity-1) parameter travels through erased Go as a
  use-once cell: `1 b T` erases to `b Lin[T]`, the body's single
  consumption takes through Use(), goplus call sites wrap arguments with
  LinOf automatically (qualified across packages), and the Lin/LinOf/Use
  trio is generated once per file needing it under a //goplus:once marker.
  goplus callers proved exactly-once statically; plain-Go callers construct
  with LinOf and a second Use panics.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Linear signatures erase to cells and calls wrap
    Given a Go+ file "res/res.gp":
      """
      package res

      import "strings"

      func Consume(1 b *strings.Builder) string {
      	return b.String()
      }
      """
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strings"

      	"example.com/demo/res"
      )

      func local(1 b *strings.Builder, c bool) string {
      	if c {
      		return b.String()
      	}
      	return b.String()
      }

      func main() {
      	var a, b strings.Builder
      	a.WriteString("hi")
      	fmt.Println(res.Consume(&a))
      	fmt.Println(local(&b, true) == "")
      }
      """
    When I run goplus with arguments "gen ./..."
    Then the exit code is 0
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      hi
      true
      """
    And the file "res/res_gp.go" contains:
      """
      func Consume(b Lin[*strings.Builder]) string {
      	return b.Use().String()
      """
    And the file "res/res_gp.go" contains:
      """
      //goplus:once
      """
    And the file "res/res_gp.go" contains:
      """
      	taken *atomic.Bool
      """
    And the file "main_gp.go" contains:
      """
      	fmt.Println(res.Consume(res.LinOf(&a)))
      """

  Scenario: A second Use panics for plain-Go callers
    Given a Go+ file "res/res.gp":
      """
      package res

      import "strings"

      func Consume(1 b *strings.Builder) string {
      	return b.String()
      }
      """
    And a file "main.go":
      """
      package main

      import (
      	"fmt"
      	"strings"

      	"example.com/demo/res"
      )

      func main() {
      	var b strings.Builder
      	cell := res.LinOf(&b)
      	_ = cell.Use()
      	defer func() {
      		fmt.Println("recovered:", recover())
      	}()
      	_ = cell.Use()
      }
      """
    When I run goplus with arguments "gen ./..."
    Then the exit code is 0
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "recovered: goplus: linear value used more than once"
