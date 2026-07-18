Feature: Lowering corpus
  A data-driven corpus pinning the exact lowered signature for a spread of
  method shapes: value/pointer receivers, generic/non-generic receivers,
  multiple type parameters, variadics, and no-result methods.

  Scenario: Method signatures lower to function signatures
    Given the package context:
      """
      type Stack[T any] struct{ items []T }
      type Registry struct{ names []string }
      type Pair[K comparable, V any] struct {
      	k K
      	v V
      }
      """
    Then these methods lower to these functions:
      | method                                                    | function                                                                  |
      | func (s Stack[T]) Filter[P any](p func(T) bool) Stack[T]  | func StackFilter[T any, P any](s Stack[T], p func(T) bool) Stack[T]       |
      | func (s *Stack[T]) Set[U any](u U, f func(U) T)           | func StackSet[T any, U any](s *Stack[T], u U, f func(U) T)                |
      | func (s Stack[T]) Append[U any](us ...U) int              | func StackAppend[T any, U any](s Stack[T], us ...U) int                   |
      | func (s Stack[T]) Empty[U any]() Stack[U]                 | func StackEmpty[T any, U any](s Stack[T]) Stack[U]                        |
      | func (r Registry) Get[V any](mk func() V) V               | func RegistryGet[V any](r Registry, mk func() V) V                        |
      | func (p Pair[K, V]) Zip[W any](w W) (K, V, W)             | func PairZip[K comparable, V any, W any](p Pair[K, V], w W) (K, V, W)     |
      | func (p Pair[A, B]) First[X any](x X) (A, X)              | func PairFirst[A comparable, B any, X any](p Pair[A, B], x X) (A, X)      |
      | func (s Stack[T]) count[U any]() int                      | func stackCount[T any, U any](s Stack[T]) int                             |
