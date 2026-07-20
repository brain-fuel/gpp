Feature: Derived folds
  Every enum derives a one-level fold by default: an <Enum>Cases struct
  with one handler per variant plus a fold function under the v0.5.1
  naming rule (bare Fold when this is the package's only deriving enum;
  two deriving enums both prefix). `//goplus:derive off` opts an enum out;
  an enum whose result arguments leave a variant's type parameters
  undetermined under the identity instantiation silently derives nothing
  (the same erasure wall as unmatchable arms). Fold dispatches ALL
  variants — it is instantiation-generic and does no GADT filtering.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: A lone enum derives a bare Fold
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      func main() {
      	fmt.Println(Fold(Some(7), OptionCases[int, string]{
      		Some: strconv.Itoa,
      		None: func() string { return "-" },
      	}))
      	var n Option[int] = None
      	fmt.Println(Fold(n, OptionCases[int, string]{
      		Some: strconv.Itoa,
      		None: func() string { return "-" },
      	}))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      7
      -
      """
    And the file "main_gp.go" contains:
      """
      // OptionCases selects one handler per Option variant for Fold.
      type OptionCases[T any, R any] struct {
      	Some func(value T) R
      	None func() R
      }

      // Fold reduces Option[T] by one-level case analysis.
      func Fold[T any, R any](o Option[T], cs OptionCases[T, R]) R {
      	switch m := any(o).(type) {
      	case Some[T]:
      		return cs.Some(m.Value)
      	case None[T]:
      		return cs.None()
      	default:
      		panic("goplus: impossible enum value in Fold")
      	}
      }
      """

  Scenario: Two deriving enums both prefix; GADT enums fold all variants
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      type Expr[T any] enum {
      	Lit(v int) Expr[int]
      	Pick(l, r Expr[T])
      }

      func main() {
      	fmt.Println(OptionFold(Some(1), OptionCases[int, string]{
      		Some: strconv.Itoa,
      		None: func() string { return "-" },
      	}))
      	var ex Expr[int] = Lit(3)
      	fmt.Println(ExprFold(ex, ExprCases[int, string]{
      		Lit:  strconv.Itoa,
      		Pick: func(l, r Expr[int]) string { return "pick" },
      	}))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      1
      3
      """

  Scenario: derive off and underivable enums release the bare name
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      type Option[T any] enum {
      	Some(value T)
      	None
      }

      //goplus:derive off
      type Hidden enum {
      	H1
      }

      type Und[T any] enum {
      	Sliced(v T) Und[[]T]
      	Straight(v T)
      }

      func main() {
      	fmt.Println(Fold(Some(7), OptionCases[int, string]{
      		Some: strconv.Itoa,
      		None: func() string { return "-" },
      	}))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "7"

  Scenario: Existential variants fold at their bounds
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      type Row enum {
      	Shown[A fmt.Stringer](v A)
      	Blank
      }

      type secs int

      func (s secs) String() string { return fmt.Sprintf("%ds", int(s)) }

      func main() {
      	fmt.Println(Fold(Shown(secs(9)), RowCases[string]{
      		Shown: func(v fmt.Stringer) string { return v.String() },
      		Blank: func() string { return "-" },
      	}))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "9s"

  Scenario: An unknown derive argument is rejected
    Given a Go+ file "main.gp":
      """
      package main

      //goplus:derive visitors
      type E enum {
      	V
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "unknown //goplus:derive argument"
    And stderr contains "supported arguments: 'off', 'gen'"
