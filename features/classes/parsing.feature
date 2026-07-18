Feature: Parsing class and instance declarations
  A class declares a set of operations over one type parameter, laws
  relating them, defaults derivable from other operations, and an embedded
  hierarchy. An instance provides named operations for one applied class.
  `class`, `instance`, and `law` are contextual: every valid Go use of
  those identifiers keeps its Go meaning.

  Scenario: The algebra shape parses
    Given a G++ file "main.gpp":
      """
      package main

      type Magma[T any] class {
      	Combine(a, b T) T
      }

      type Semigroup[T any] class {
      	Magma[T]
      	law Assoc(a, b, c T) { return Combine(Combine(a, b), c) == Combine(a, Combine(b, c)) }
      }

      type Monoid[T any] class {
      	Semigroup[T]
      	Empty() T
      	law LeftId(a T) { return Combine(Empty(), a) == a }
      	law RightId(a T) { return Combine(a, Empty()) == a }
      }

      type Group[T any] class {
      	Monoid[T]
      	Invert(a T) T
      	LeftDiv(a, b T) T { return Combine(Invert(b), a) }
      	RightDiv(a, b T) T { return Combine(a, Invert(b)) }
      }

      instance IntAdd Group[int] {
      	Combine(a, b int) int { return a + b }
      	Empty() int { return 0 }
      	Invert(a int) int { return -a }
      }

      instance SliceConcat[T any] Monoid[[]T] {
      	Combine(a, b []T) []T { return append(append([]T{}, a...), b...) }
      	Empty() []T { return nil }
      }
      """
    When I parse it
    Then parsing succeeds with 4 classes and 2 instances
    And class 0 has 0 embeds, 1 op, and 0 laws
    And class 1 has 1 embed, 0 ops, and 1 law
    And class 2 has 1 embed, 1 op, and 2 laws
    And class 3 has 1 embed, 3 ops, and 0 laws
    And class 3 op "LeftDiv" has a default body
    And instance 0 is named "IntAdd" for class "Group[int]"
    And instance 1 is named "SliceConcat" for class "Monoid[[]T]"

  Scenario: class, instance, and law stay ordinary identifiers in Go code
    Given a G++ file "main.gpp":
      """
      package main

      type class struct{ law int }

      var instance = class{law: 1}

      func f(law int) int {
      	instance := law + 1
      	return instance
      }
      """
    When I parse it
    Then parsing succeeds with 0 classes and 0 instances

  Scenario: An identifier type named class is not claimed without a brace
    Given a G++ file "main.gpp":
      """
      package main

      type class int

      type T class
      """
    When I parse it
    Then parsing succeeds with 0 classes and 0 instances

  Scenario: A law requires a body
    Given a G++ file "main.gpp":
      """
      package main

      type Semigroup[T any] class {
      	Combine(a, b T) T
      	law Assoc(a, b, c T)
      }
      """
    When I parse it
    Then parsing fails with an error containing "a law requires a body"

  Scenario: A class cannot be a type alias
    Given a G++ file "main.gpp":
      """
      package main

      type Semigroup[T any] = class {
      	Combine(a, b T) T
      }
      """
    When I parse it
    Then parsing fails with an error containing "class declarations cannot be type aliases"

  Scenario: An instance head must apply the class
    Given a G++ file "main.gpp":
      """
      package main

      instance X Monoid {
      	Combine(a, b int) int { return a + b }
      }
      """
    When I parse it
    Then parsing fails with an error containing "an instance names a fully applied class; write Monoid[int]"

  Scenario: Instance members require bodies
    Given a G++ file "main.gpp":
      """
      package main

      instance X Monoid[int] {
      	Combine(a, b int) int
      }
      """
    When I parse it
    Then parsing fails with an error containing "instance members must have a body"
