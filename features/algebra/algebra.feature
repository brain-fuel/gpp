Feature: The std/algebra hierarchy
  goforge.dev/goplus/std/algebra ships the eight classes Magma through
  Group with their laws, stock instances, and the generic helpers
  Accumulate and FoldMap. Instances resolve implicitly; the Group
  instance IntAdd satisfies every weaker constraint by subsumption, and
  its divisions come from Group's defaults.

  Background:
    Given a module "example.com/demo" using the goplus standard library

  Scenario: Accumulate and FoldMap over stock instances
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/algebra"
      )

      var _ = algebra.IntAdd

      func main() {
      	fmt.Println(algebra.Accumulate(algebra.StringConcat, []string{"go", "pp"}))
      	fmt.Println(algebra.Accumulate(algebra.BoolAnd, []bool{true, true}))
      	fmt.Println(algebra.Accumulate(algebra.BoolOr, []bool{false, false}))
      	fmt.Println(algebra.Accumulate(algebra.SliceConcat[int](), [][]int{{1}, {2, 3}}))
      	fmt.Println(algebra.FoldMap(algebra.IntMul, []string{"ab", "cde"}, func(s string) int { return len(s) }))
      	fmt.Println(algebra.IntAdd.LeftDiv(10, 4), algebra.IntAdd.RightDiv(10, 4))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      gopp
      true
      false
      [1 2 3]
      6
      6 6
      """

  Scenario: Local instances of std classes dispatch implicitly, laws generate
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/algebra"
      )

      // FloatAdd is addition over float64.
      //goplus:laws off
      instance FloatAdd algebra.Group[float64] {
      	Combine(a, b float64) float64 { return a + b }
      	Empty() float64 { return 0 }
      	Invert(a float64) float64 { return -a }
      }

      func main() {
      	fmt.Println(algebra.Accumulate([]float64{1.5, 2.5}))
      	fmt.Println(FloatAdd.LeftDiv(10, 4))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      4
      6
      """

  Scenario: int has two monoids, and implicit resolution refuses to guess
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/algebra"
      )

      var _ = algebra.IntAdd

      func main() {
      	fmt.Println(algebra.Accumulate([]int{2, 3, 4}))
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "ambiguous instance for Monoid[int]"
    And stderr contains "IntAdd"
    And stderr contains "IntMul"

  Scenario: Naming the structure disambiguates
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/algebra"
      )

      func main() {
      	fmt.Println(algebra.Accumulate(algebra.IntAdd, []int{2, 3, 4}))
      	fmt.Println(algebra.Accumulate(algebra.IntMul, []int{2, 3, 4}))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      9
      24
      """
    And the file "main_gp.go" contains:
      """
      	fmt.Println(algebra.Accumulate(algebra.IntAdd.AsMonoid(), []int{2, 3, 4}))
      	fmt.Println(algebra.Accumulate(algebra.IntMul, []int{2, 3, 4}))
      """

  Scenario: MinInt and MaxInt are ambiguous for a bare Semigroup constraint
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/algebra"
      )

      var _ = algebra.MinInt

      func Squash[T algebra.Semigroup](xs []T) T {
      	acc := xs[0]
      	for _, x := range xs[1:] {
      		acc = Combine(acc, x)
      	}
      	return acc
      }

      func main() {
      	fmt.Println(Squash([]int{5, 2, 9}))
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "ambiguous instance for Semigroup[int]"
    And stderr contains "pass a witness explicitly"
