Feature: Derived rapid generators
  Every monomorphic enum can derive Gen<Enum>(t *rapid.T): variants
  chosen uniformly, fields generated recursively (sibling enums through
  their own generators, depth-bounded to leaf variants at the bottom).
  Derivation is default-on but EMISSION is demand-driven — law tests
  that need one, or `//gpp:derive gen` producing a per-package
  gpp_gen_test.go — so rapid never enters a module's dependencies
  uninvited.

  Scenario: Opted-in enums emit generators that respect the depth bound
    Given a module "example.com/demo" using rapid for law tests
    And a G++ file "main.gpp":
      """
      package main

      //gpp:derive gen
      type Strategy enum {
      	Eager
      	Deferred(where Where, on Trigger)
      	Live
      }

      //gpp:derive gen
      type Where enum {
      	Server
      	Client
      }

      //gpp:derive gen
      type Trigger enum {
      	OnLoad
      	OnVisible
      	OnHover
      }

      //gpp:derive gen
      type List enum {
      	Empty
      	Cons(head int, tail List)
      }

      func main() {}
      """
    And a file "gen_use_test.go":
      """
      package main

      import (
      	"testing"

      	"pgregory.net/rapid"
      )

      func TestGeneratorsProduceValues(t *testing.T) {
      	rapid.Check(t, func(rt *rapid.T) {
      		_ = GenStrategy(rt)
      		l := GenList(rt)
      		depth := 0
      		for {
      			c, ok := any(l).(Cons)
      			if !ok {
      				break
      			}
      			l = c.Tail
      			depth++
      		}
      		if depth > 10 {
      			rt.Fatalf("depth bound violated: %d", depth)
      		}
      	})
      }
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 0
    And the file "gpp_gen_test.go" contains:
      """
      func GenStrategy(t *rapid.T) Strategy {
      """
    And the file "gpp_gen_test.go" contains:
      """
      		return Deferred{Where: genWhereDepth(t, depth-1), On: genTriggerDepth(t, depth-1)}
      """
    When I run gpp with arguments "test ."
    Then the exit code is 0

  Scenario: No demand, no rapid — plain enums emit no generator file
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """
    And a G++ file "main.gpp":
      """
      package main

      type Color enum {
      	Red
      	Green
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 0
    And the file "gpp_gen_test.go" does not exist

  Scenario: A generic enum cannot derive a generator
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """
    And a G++ file "main.gpp":
      """
      package main

      //gpp:derive gen
      type Box[T any] enum {
      	Full(v T)
      	Vacant
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "enum Box cannot derive a generator (type parameters, indices, or no leaf variant)"
