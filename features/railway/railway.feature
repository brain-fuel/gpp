Feature: Railway-oriented pipelines
  When the value flowing through |> is a Result[T, E], stages lift by
  shape, first match wins: dot segments receive the raw Result; a stage
  accepting the Result stays a direct call; T→Result[U, E] binds;
  T→(U, error) adapts through result.Of (error railways only); T→U maps;
  T→() tees on the Ok path only. Err bypasses every lifted stage. Stage
  extra arguments close over in a function literal, so they evaluate on
  the Ok path only. A (T, error) HEAD keeps Go's spread rule — the rail
  starts when a Result value flows.

  Background:
    Given a module "example.com/demo" using the goplus standard library

  Scenario: The canonical mixed chain
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      	"strings"

      	"goforge.dev/goplus/std/result"
      )

      var audits []int

      func validate(s string) result.Result[string, error] {
      	if s == "" {
      		return result.Err[string, error]{Err: fmt.Errorf("empty input")}
      	}
      	return result.Ok[string, error]{Value: s}
      }

      func audit(n int) {
      	audits = append(audits, n)
      }

      func load(s string) int {
      	return s |> validate |> strings.TrimSpace |> strconv.Atoi |> audit |> .UnwrapOr(0)
      }

      func main() {
      	fmt.Println(load(" 21 "))
      	fmt.Println(load(""))
      	fmt.Println(load("bad"))
      	fmt.Println(audits)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      21
      0
      0
      [21]
      """
    And the file "main_gp.go" contains:
      """
      	return result.UnwrapOr(result.Tee(result.Bind(result.Map(validate(s), strings.TrimSpace), func(__gp_p string) result.Result[int, error] { return result.Of(strconv.Atoi(__gp_p)) }), audit), 0)
      """

  Scenario: Stage extra arguments evaluate on the Ok path only
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/result"
      )

      var evals int

      func suffix() string {
      	evals++
      	return "!"
      }

      func validate(s string) result.Result[string, error] {
      	if s == "" {
      		return result.Err[string, error]{Err: fmt.Errorf("empty")}
      	}
      	return result.Ok[string, error]{Value: s}
      }

      func addSuffix(s, suf string) string { return s + suf }

      func decorate(s string) string {
      	return s |> validate |> addSuffix(_, suffix()) |> .UnwrapOr("?")
      }

      func main() {
      	fmt.Println(decorate("hi"), evals)
      	fmt.Println(decorate(""), evals)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "hi! 1"
    And stdout contains "? 1"

  Scenario: A stage accepting the Result itself stays a direct call
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/result"
      )

      func ok(n int) result.Result[int, error] { return result.Ok[int, error]{Value: n} }

      func describe(r result.Result[int, error]) string {
      	return fmt.Sprintf("ok=%v", result.IsOk(r))
      }

      func main() {
      	fmt.Println(ok(1) |> describe)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "ok=true"
    And the file "main_gp.go" contains:
      """
      	fmt.Println(describe(ok(1)))
      """

  Scenario: A (T, error) head keeps the spread rule and result.Of opens the rail
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"goforge.dev/goplus/std/result"
      )

      func double(n int) int { return n * 2 }

      func calc(s string) int {
      	return strconv.Atoi(s) |> result.Of |> double |> .UnwrapOr(-1)
      }

      func main() {
      	fmt.Println(calc("21"))
      	fmt.Println(calc("bad"))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      42
      -1
      """

  Scenario: Mid-pipe ? leaves the railway
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/result"
      )

      func validate(s string) result.Result[string, error] {
      	if s == "" {
      		return result.Err[string, error]{Err: fmt.Errorf("empty")}
      	}
      	return result.Ok[string, error]{Value: s}
      }

      func exclaim(s string) string { return s + "!" }

      func shout(s string) (string, error) {
      	out := s |> validate? |> exclaim
      	return out, nil
      }

      func main() {
      	fmt.Println(shout("hi"))
      	_, err := shout("")
      	fmt.Println(err)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "hi! <nil>"
    And stdout contains "empty"

  Scenario: Binding a stage with a different error type is an error
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/result"
      )

      type ErrA struct{}
      type ErrB struct{}

      func (ErrA) Error() string { return "a" }
      func (ErrB) Error() string { return "b" }

      func stepA(n int) result.Result[int, ErrA] { return result.Ok[int, ErrA]{Value: n} }
      func stepB(n int) result.Result[int, ErrB] { return result.Ok[int, ErrB]{Value: n} }

      func main() {
      	fmt.Println(stepA(1) |> stepB)
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "it returns a Result with error type ErrB, but the pipeline's error type is ErrA"

  Scenario: Adapting a Go-shaped stage onto a typed-error railway is an error
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"goforge.dev/goplus/std/result"
      )

      type ErrA struct{}

      func (ErrA) Error() string { return "a" }

      func stepA(s string) result.Result[string, ErrA] { return result.Ok[string, ErrA]{Value: s} }

      func main() {
      	fmt.Println(stepA("1") |> strconv.Atoi)
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "only railways with error type error adapt Go-shaped stages"

  Scenario: A stage returning several plain values cannot lift
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/result"
      )

      func multi(n int) (int, int) { return n, n }

      func ok(n int) result.Result[int, error] { return result.Ok[int, error]{Value: n} }

      func main() {
      	fmt.Println(ok(1) |> multi)
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "railway stages return a Result, a single value, (value, error), or nothing"
