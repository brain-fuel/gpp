Feature: Lowered names collide predictably
  A lowered function keeps its method's own name while that name is unique
  in the package. Colliders — two types sharing a method name, or a bare
  name already taken by an authored declaration — ALL fall back to the
  receiver-prefixed form. A collision that survives prefixing is a hard
  error naming both origins.

  Scenario: Two types sharing a method name both prefix
    Given a Go+ file "shared.gp":
      """
      package shared

      type Stack[T any] struct{ items []T }
      type Ring[T any] struct{ items []T }

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	return Stack[U]{}
      }

      func (r Ring[T]) Map[U any](f func(T) U) Ring[U] {
      	return Ring[U]{}
      }
      """
    When I compute lowered names
    Then the lowered names are "StackMap, RingMap"

  Scenario: A bare name taken by an authored declaration prefixes
    Given a Go+ file "stack.gp":
      """
      package stack

      type Stack[T any] struct{ items []T }

      func Map() {}

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	return Stack[U]{}
      }
      """
    When I compute lowered names
    Then the lowered names are "StackMap"

  Scenario: A collision that survives prefixing is an error
    Given a Go+ file "stack.gp":
      """
      package stack

      type Stack[T any] struct{ items []T }

      func Map() {}

      func StackMap() {}

      func (s Stack[T]) Map[U any](f func(T) U) Stack[U] {
      	return Stack[U]{}
      }
      """
    When I compute lowered names
    Then name generation fails with an error containing "generated name StackMap"
    And name generation fails with an error containing "collides"
    And name generation fails with an error containing "rename"

  Scenario: Case folding makes unexported twins prefix, then collide
    Given a Go+ file "fold.gp":
      """
      package fold

      type Ring[T any] struct{}
      type ring[T any] struct{}

      func (r ring[T]) Rotate[U any]() {}
      func (r Ring[T]) rotate[U any]() {}
      """
    When I compute lowered names
    Then name generation fails with an error containing "generated name ringRotate"
