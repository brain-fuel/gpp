Feature: Interface delegation
  A struct field marked with the trailing `delegate` keyword must have an
  interface type; the outer type gains a generated value-receiver
  forwarding method for every interface method it does not otherwise
  declare — authored anywhere in the package counts as an override. Two
  delegate fields offering the same method is an error naming both. A
  delegate field is NOT embedded: no promotion happens beyond the
  generated forwarders.

  Background:
    Given a file "go.mod":
      """
      module example.com/demo

      go 1.24
      """

  Scenario: Forwarders generate; overrides win
    Given a G++ file "main.gpp":
      """
      package main

      import (
      	"fmt"
      	"log"
      	"os"
      )

      type Store interface {
      	Get(k string) (string, error)
      	Put(k, v string) error
      	Len() int
      }

      type memStore struct{ m map[string]string }

      func (s *memStore) Get(k string) (string, error) { return s.m[k], nil }
      func (s *memStore) Put(k, v string) error        { s.m[k] = v; return nil }
      func (s *memStore) Len() int                     { return len(s.m) }

      type Logged struct {
      	inner Store delegate
      	log   *log.Logger
      }

      // Put is overridden: it logs, then forwards.
      func (l Logged) Put(k, v string) error {
      	l.log.Println("put", k)
      	return l.inner.Put(k, v)
      }

      func main() {
      	ms := &memStore{m: map[string]string{}}
      	l := Logged{inner: ms, log: log.New(os.Stdout, "", 0)}
      	var s Store = l
      	_ = s.Put("a", "1")
      	v, _ := s.Get("a")
      	fmt.Println(v, s.Len())
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains:
      """
      put a
      1 1
      """
    And the file "main_gpp.go" contains:
      """
      //gpp:delegate Logged.inner
      func (l Logged) Get(p0 string) (string, error) { return l.inner.Get(p0) }
      """
    And the file "main_gpp.go" contains:
      """
      //gpp:delegate Logged.inner
      func (l Logged) Len() int { return l.inner.Len() }
      """

  Scenario: Generic outer types forward with their type parameters
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Source[T any] interface {
      	Next() (T, bool)
      }

      type sliceSource[T any] struct {
      	xs []T
      	i  int
      }

      func (s *sliceSource[T]) Next() (T, bool) {
      	if s.i >= len(s.xs) {
      		var zero T
      		return zero, false
      	}
      	v := s.xs[s.i]
      	s.i++
      	return v, true
      }

      type Counted[T any] struct {
      	src Source[T] delegate
      	N   int
      }

      func main() {
      	c := Counted[int]{src: &sliceSource[int]{xs: []int{5, 6}}}
      	var s Source[int] = c
      	a, _ := s.Next()
      	b, _ := s.Next()
      	fmt.Println(a, b)
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "5 6"
    And the file "main_gpp.go" contains:
      """
      //gpp:delegate Counted.src
      func (c Counted[T]) Next() (T, bool) { return c.src.Next() }
      """

  Scenario: Two delegates offering one method is an error
    Given a G++ file "main.gpp":
      """
      package main

      type Reader interface {
      	Read() string
      }

      type Both struct {
      	a Reader delegate
      	b Reader delegate
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "type Both delegates Read through both a and b; declare Read on Both to take ownership"

  Scenario: A non-interface delegate type is an error
    Given a G++ file "main.gpp":
      """
      package main

      type Impl struct{}

      type Wrapper struct {
      	inner Impl delegate
      }

      func main() {}
      """
    When I run gpp with arguments "gen ."
    Then the exit code is 2
    And stderr contains "delegate field inner of Wrapper must have an interface type"

  Scenario: Delegation does not promote unrelated members
    Given a G++ file "main.gpp":
      """
      package main

      import "fmt"

      type Named interface {
      	Name() string
      }

      type person struct{ n string }

      func (p person) Name() string { return p.n }
      func (p person) Secret() int  { return 42 }

      type Badge struct {
      	who Named delegate
      }

      func main() {
      	b := Badge{who: person{n: "ada"}}
      	fmt.Println(b.Name())
      }
      """
    When I run gpp with arguments "run ."
    Then the exit code is 0
    And stdout contains "ada"
