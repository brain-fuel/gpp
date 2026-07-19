Feature: Constraint lowering and implicit instance dispatch
  A class constraint on a function type parameter lowers to a leading
  witness value parameter; call sites receive the resolved instance
  implicitly. Candidates are the current package's instances plus exported
  instances of the file's direct imports. A stronger instance satisfies a
  weaker constraint through its upcast (full subsumption); ambiguity is a
  hard error naming the candidates; the escape hatch is calling the
  lowered signature directly.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: The whole algebra dispatches
    Given a G++ file "main.gpp":
      """
      package main

      import (
      	"fmt"
      	"reflect"
      )

      type Magma[T any] class {
      	Combine(a, b T) T
      }

      type Semigroup[T any] class {
      	Magma[T]
      	law Assoc(a, b, c T) { return reflect.DeepEqual(Combine(Combine(a, b), c), Combine(a, Combine(b, c))) }
      }

      type Monoid[T any] class {
      	Semigroup[T]
      	Empty() T
      	law LeftId(a T) { return reflect.DeepEqual(Combine(Empty(), a), a) }
      }

      type Group[T any] class {
      	Monoid[T]
      	Invert(a T) T
      	LeftDiv(a, b T) T { return Combine(Invert(b), a) }
      }

      instance IntAdd Group[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      	Invert(a int) int { return -a }
      }

      instance StringConcat Monoid[string] {
      	Combine(a, b string) string { return a + b }
      	Empty() string { return "" }
      }

      instance SliceConcat[T any] Monoid[[]T] {
      	Combine(a, b []T) []T { return append(append([]T{}, a...), b...) }
      	Empty() []T { return nil }
      }

      func Accumulate[T Monoid](xs []T) T {
      	acc := Empty()
      	for _, x := range xs {
      		acc = Combine(acc, x)
      	}
      	return acc
      }

      func main() {
      	fmt.Println(Accumulate([]int{1, 2, 3}))
      	fmt.Println(Accumulate([]string{"go", "pp"}))
      	fmt.Println(Accumulate([][]int{{1}, {2, 3}}))
      	fmt.Println(IntAdd.LeftDiv(10, 4))
      	fmt.Println(IntAdd.AsSemigroup().LawAssoc(1, 2, 3), IntAdd.AsMonoid().LawLeftId(9))
      	fmt.Println(Accumulate(SliceConcat[int](), [][]int{{7}, {8}}))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      6
      gopp
      [1 2 3]
      6
      true true
      [7 8]
      """
    And the file "main_gpp.go" contains:
      """
      func Accumulate[T any](monoid Monoid[T], xs []T) T {
      	acc := monoid.Empty()
      	for _, x := range xs {
      		acc = monoid.Combine(acc, x)
      	}
      	return acc
      }
      """
    And the file "main_gpp.go" contains:
      """
      	fmt.Println(Accumulate(IntAdd.AsMonoid(), []int{1, 2, 3}))
      """
    And the file "main_gpp.go" contains:
      """
      	w.LeftDiv = func(__gpp_a0 int, __gpp_a1 int) int { return w.DefaultLeftDiv(__gpp_a0, __gpp_a1) }
      """

  Scenario: Constrained functions thread their own dictionaries, upcast as needed
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Semigroup[T any] class {
      	Combine(a, b T) T
      }

      type Monoid[T any] class {
      	Semigroup[T]
      	Empty() T
      }

      instance IntAdd Monoid[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      }

      func Twice[T Semigroup](x T) T {
      	return x.Combine(x)
      }

      func Total[T Monoid](xs []T) T {
      	acc := Empty()
      	for _, x := range xs {
      		acc = Combine(acc, Twice(x))
      	}
      	return acc
      }

      func main() {
      	fmt.Println(Total([]int{1, 2}))
      	fmt.Println([]int{3, 4} |> Total)
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      6
      14
      """
    And the file "main_gpp.go" contains:
      """
      		acc = monoid.Combine(acc, Twice(monoid.AsSemigroup(), x))
      """

  Scenario: Multiple constraints on one parameter pass multiple witnesses
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Monoid[T any] class {
      	Combine(a, b T) T
      	Empty() T
      }

      type Printer[T any] class {
      	Print(a T) string
      }

      instance IntAdd Monoid[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      }

      instance IntShow Printer[int] {
      	Print(a int) string { return fmt.Sprintf("<%d>", a) }
      }

      func Describe[T interface{ Monoid; Printer }](xs []T) string {
      	acc := Empty()
      	for _, x := range xs {
      		acc = Combine(acc, x)
      	}
      	return Print(acc)
      }

      func main() {
      	fmt.Println(Describe([]int{1, 2, 3}))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "<6>"

  Scenario: Ambiguous instances are a hard error naming the candidates
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Monoid[T any] class {
      	Combine(a, b T) T
      	Empty() T
      }

      instance IntAdd Monoid[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      }

      instance IntMul Monoid[int] {
      	Combine(a, b int) int { return a * b }
      	Empty() int { return 1 }
      }

      func Accumulate[T Monoid](xs []T) T {
      	acc := Empty()
      	for _, x := range xs {
      		acc = Combine(acc, x)
      	}
      	return acc
      }

      func main() {
      	fmt.Println(Accumulate([]int{1, 2, 3}))
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "ambiguous instance for Monoid[int]: candidates IntAdd, IntMul; pass a witness explicitly"

  Scenario: The escape hatch resolves ambiguity
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Monoid[T any] class {
      	Combine(a, b T) T
      	Empty() T
      }

      instance IntAdd Monoid[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      }

      instance IntMul Monoid[int] {
      	Combine(a, b int) int { return a * b }
      	Empty() int { return 1 }
      }

      func Accumulate[T Monoid](xs []T) T {
      	acc := Empty()
      	for _, x := range xs {
      		acc = Combine(acc, x)
      	}
      	return acc
      }

      func main() {
      	fmt.Println(Accumulate(IntAdd, []int{1, 2, 3}), Accumulate(IntMul, []int{1, 2, 3}))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "6 6"

  Scenario: No instance in scope is a guided error
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Monoid[T any] class {
      	Combine(a, b T) T
      	Empty() T
      }

      func Accumulate[T Monoid](xs []T) T {
      	acc := Empty()
      	for _, x := range xs {
      		acc = Combine(acc, x)
      	}
      	return acc
      }

      func main() {
      	fmt.Println(Accumulate([]float64{1, 2}))
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "no instance of Monoid[float64] is in scope for this call; declare one, import a package that provides one, or pass a witness explicitly"

  Scenario: An explicit witness of a stronger class upcasts automatically
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Semigroup[T any] class {
      	Combine(a, b T) T
      }

      type Monoid[T any] class {
      	Semigroup[T]
      	Empty() T
      }

      instance IntAdd Monoid[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      }

      instance IntMul Monoid[int] {
      	Combine(a, b int) int { return a * b }
      	Empty() int { return 1 }
      }

      func Squash[T Semigroup](a, b, c T) T {
      	return Combine(Combine(a, b), c)
      }

      func main() {
      	fmt.Println(Squash(IntAdd, 2, 3, 4), Squash(IntMul, 2, 3, 4))
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "9 24"
    And the file "main_gpp.go" contains:
      """
      	fmt.Println(Squash(IntAdd.AsSemigroup(), 2, 3, 4), Squash(IntMul.AsSemigroup(), 2, 3, 4))
      """
