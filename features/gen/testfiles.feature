Feature: Go+ test sources
  foo_test.gp emits foo_gp_test.go — still a _test.go file to the go
  tool — so tests are written in full Go+: constructors, matches,
  pipelines, and derived generators all work in test code.

  Scenario: A test written in Go+ runs under goplus test
    Given a module "example.com/demo" using rapid for law tests
    And a Go+ file "main.gp":
      """
      package main

      type Color enum {
      	Red
      	Blue(depth int)
      }

      func main() {}
      """
    And a Go+ file "main_test.gp":
      """
      package main

      import "testing"

      func TestMatchInGoplusTest(t *testing.T) {
      	var c Color = Blue(3)
      	match c {
      	case Blue(d):
      		if d != 3 {
      			t.Fatal("wrong depth")
      		}
      	case Red():
      		t.Fatal("wrong variant")
      	}
      }
      """
    When I run goplus with arguments "gen ."
    Then the exit code is 0
    And the file "main_gp_test.go" contains:
      """
      func TestMatchInGoplusTest(t *testing.T) {
      """
    When I run goplus with arguments "test ."
    Then the exit code is 0
