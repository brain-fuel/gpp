Feature: Postfix ? failure propagation
  `e?` propagates failure to the enclosing function. An (…, error)-returning
  function early-returns zero values and the error; a Result-returning
  function returns Err — via result.Unpack when its error type is `error`,
  or a variant assertion that preserves a typed error otherwise. Operands
  may be Result values, (…, error)-shaped calls, or bare errors. The check
  hoists before the enclosing statement; on a pipeline stage, ? applies to
  the stage result.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: The whole right-hand side of := unpacks in place (fast path)
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"os"
      	"strconv"
      )

      func readNum(path string) (int, error) {
      	data := os.ReadFile(path)?
      	n := strconv.Atoi(string(data))?
      	return n * 2, nil
      }

      func main() {
      	os.WriteFile("num.txt", []byte("21"), 0o644)
      	n, err := readNum("num.txt")
      	fmt.Println(n, err)
      	_, err = readNum("missing.txt")
      	fmt.Println(err != nil)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "42 <nil>"
    And stdout contains "true"
    And the file "main_gp.go" contains:
      """
      	data, __gp_err0 := os.ReadFile(path)
      	if __gp_err0 != nil {
      		return *new(int), __gp_err0
      	}
      	n, __gp_err1 := strconv.Atoi(string(data))
      	if __gp_err1 != nil {
      		return *new(int), __gp_err1
      	}
      	return n * 2, nil
      """

  Scenario: A nested ? hoists a temp before the enclosing statement
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      func label(s string) (string, error) {
      	return fmt.Sprintf("n=%d", strconv.Atoi(s)?), nil
      }

      func main() {
      	l, err := label("7")
      	fmt.Println(l, err)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "n=7 <nil>"
    And the file "main_gp.go" contains:
      """
      	__gp_t0, __gp_err0 := strconv.Atoi(s)
      	if __gp_err0 != nil {
      		return *new(string), __gp_err0
      	}
      	return fmt.Sprintf("n=%d", __gp_t0), nil
      """

  Scenario: A multi-value operand as the whole right-hand side
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func pair(ok bool) (int, string, error) {
      	if !ok {
      		return 0, "", fmt.Errorf("no pair")
      	}
      	return 1, "a", nil
      }

      func use() (string, error) {
      	n, s := pair(true)?
      	return fmt.Sprintf("%d%s", n, s), nil
      }

      func main() {
      	v, err := use()
      	fmt.Println(v, err)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "1a <nil>"

  Scenario: A Result operand in an (…, error) function goes through Unpack
    Given a module "example.com/demo" using the goplus standard library
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"goforge.dev/goplus/std/result"
      )

      func parse(s string) result.Result[int, error] {
      	return result.Of(strconv.Atoi(s))
      }

      func goShape(s string) (int, error) {
      	n := parse(s)?
      	return n + 1, nil
      }

      func main() {
      	n, err := goShape("41")
      	fmt.Println(n, err)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "42 <nil>"
    And the file "main_gp.go" contains:
      """
      	__gp_t0, __gp_err0 := result.Unpack(parse(s))
      	if __gp_err0 != nil {
      		return *new(int), __gp_err0
      	}
      """

  Scenario: A Result-returning function returns Err (Unpack form)
    Given a module "example.com/demo" using the goplus standard library
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"goforge.dev/goplus/std/result"
      )

      func parse(s string) result.Result[int, error] {
      	return result.Of(strconv.Atoi(s))
      }

      func double(s string) result.Result[int, error] {
      	n := parse(s)?
      	return result.Ok[int, error]{Value: n * 2}
      }

      func fromGoShape(s string) result.Result[int, error] {
      	n := strconv.Atoi(s)?
      	return result.Ok[int, error]{Value: n + 1}
      }

      func main() {
      	fmt.Println(result.UnwrapOr(double("21"), -1))
      	fmt.Println(result.IsErr(double("nope")))
      	fmt.Println(result.UnwrapOr(fromGoShape("41"), -1))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      42
      true
      42
      """
    And the file "main_gp.go" contains:
      """
      	__gp_t0, __gp_err0 := result.Unpack(parse(s))
      	if __gp_err0 != nil {
      		return result.Err[int, error]{Err: __gp_err0}
      	}
      """

  Scenario: A typed error rail is preserved through a variant assertion
    Given a module "example.com/demo" using the goplus standard library
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"goforge.dev/goplus/std/result"
      )

      type ParseErr struct{ Line int }

      func (e ParseErr) Error() string { return fmt.Sprintf("bad line %d", e.Line) }

      func step(n int) result.Result[int, ParseErr] {
      	if n < 0 {
      		return result.Err[int, ParseErr]{Err: ParseErr{Line: n}}
      	}
      	return result.Ok[int, ParseErr]{Value: n * 2}
      }

      func chain(n int) result.Result[string, ParseErr] {
      	v := step(n)?
      	return result.Ok[string, ParseErr]{Value: fmt.Sprintf("v=%d", v)}
      }

      func main() {
      	fmt.Println(result.UnwrapOr(chain(21), "?"))
      	fmt.Println(result.MapError(chain(-1), func(e ParseErr) ParseErr { return e }))
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "v=42"
    And stdout contains "bad line -1"
    And the file "main_gp.go" contains:
      """
      	__gp_r0 := step(n)
      	if result.IsErr(__gp_r0) {
      		return result.Err[string, ParseErr]{Err: any(__gp_r0).(result.Err[int, ParseErr]).Err}
      	}
      	__gp_t0 := any(__gp_r0).(result.Ok[int, ParseErr]).Value
      """

  Scenario: The std/result import is added when a file needs one
    Given a module "example.com/demo" using the goplus standard library
    And a Go+ file "lib/lib.gp":
      """
      package lib

      import (
      	"strconv"

      	"goforge.dev/goplus/std/result"
      )

      func Parse(s string) result.Result[int, error] {
      	return result.Of(strconv.Atoi(s))
      }
      """
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"

      	"example.com/demo/lib"
      )

      func plain(s string) (int, error) {
      	n := lib.Parse(s)?
      	return n, nil
      }

      func main() {
      	n, err := plain("7")
      	fmt.Println(n, err)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "7 <nil>"
    And the file "main_gp.go" contains:
      """
      import "goforge.dev/goplus/std/result"
      """

  Scenario: A bare error operand propagates as a statement
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"errors"
      	"fmt"
      )

      func guard(n int) (int, error) {
      	if n < 0 {
      		errors.New("negative")?
      	}
      	return n, nil
      }

      func main() {
      	fmt.Println(guard(5))
      	_, err := guard(-5)
      	fmt.Println(err)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "5 <nil>"
    And stdout contains "negative"
    And the file "main_gp.go" contains:
      """
      		if __gp_err0 := errors.New("negative"); __gp_err0 != nil {
      			return *new(int), __gp_err0
      		}
      """

  Scenario: On a pipeline stage, ? applies to the stage result
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      func double(n int) int { return n * 2 }

      func calc(s string) (int, error) {
      	n := s |> strconv.Atoi? |> double
      	return n, nil
      }

      func main() {
      	n, err := calc("21")
      	fmt.Println(n, err)
      	_, err = calc("x")
      	fmt.Println(err != nil)
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains "42 <nil>"
    And stdout contains "true"

  Scenario: ? and a hand-written err check are equivalent (oracle)
    Given a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"
      )

      func viaTry(s string) (int, error) {
      	n := strconv.Atoi(s)?
      	return n * 2, nil
      }

      func viaHand(s string) (int, error) {
      	n, err := strconv.Atoi(s)
      	if err != nil {
      		return 0, err
      	}
      	return n * 2, nil
      }

      func main() {
      	for _, s := range []string{"21", "x", "-3", ""} {
      		a, aerr := viaTry(s)
      		b, berr := viaHand(s)
      		fmt.Println(a == b, (aerr == nil) == (berr == nil))
      	}
      }
      """
    When I run goplus with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      true true
      true true
      true true
      true true
      """

  Scenario: ? in a function with no failure channel is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "strconv"

      func f(s string) int {
      	return strconv.Atoi(s)?
      }

      func main() { _ = f("1") }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "the enclosing function returns neither (…, error) nor a Result"

  Scenario: A ? operand that cannot fail is an error
    Given a Go+ file "main.gp":
      """
      package main

      func f(n int) (int, error) {
      	return n?, nil
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "the ? operand must be a Result value, an (…, error) call, or an error; it has type int"

  Scenario: A multi-value operand outside a whole assignment or return is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "fmt"

      func two() (int, string, error) { return 1, "a", nil }

      func f() (string, error) {
      	return fmt.Sprint(two()?), nil
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "can only be the whole right-hand side of an assignment or the whole return operand"

  Scenario: ? on a whole deferred call is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "os"

      func f() error {
      	defer os.Remove("x")?
      	return nil
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "? cannot apply to a whole deferred call"

  Scenario: ? in a for condition is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "strconv"

      func f(s string) (int, error) {
      	total := 0
      	for i := 0; i < strconv.Atoi(s)?; i++ {
      		total += i
      	}
      	return total, nil
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "? cannot appear in a for condition or post statement"

  Scenario: ? on the right of && is an error
    Given a Go+ file "main.gp":
      """
      package main

      import "strconv"

      func f(s string, ok bool) (int, error) {
      	if ok && strconv.Atoi(s)? > 0 {
      		return 1, nil
      	}
      	return 0, nil
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "? cannot appear on the right side of &&"

  Scenario: A Go-shaped operand cannot enter a typed-error Result function
    Given a module "example.com/demo" using the goplus standard library
    And a Go+ file "main.gp":
      """
      package main

      import (
      	"fmt"
      	"strconv"

      	"goforge.dev/goplus/std/result"
      )

      type ParseErr struct{ Line int }

      func (e ParseErr) Error() string { return fmt.Sprintf("bad line %d", e.Line) }

      func f(s string) result.Result[int, ParseErr] {
      	n := strconv.Atoi(s)?
      	return result.Ok[int, ParseErr]{Value: n}
      }

      func main() {}
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 2
    And stderr contains "can only propagate into a function whose Result error type is error"
