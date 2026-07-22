// Package validate provides typed, composable validation rules whose
// predicates survive successful validation as erased dependent indices.
package validate

import "strings"

// Predicate is first-order index data. Named identifies an atomic proposition;
// Both is an ordered, collision-free conjunction.
//goplus:derive off
type Predicate enum {
	Named(ID int)
	Both(Left Predicate, Right Predicate)
}

// PredicateAtomID and PredicateBothID form a disjoint, collision-free natural
// encoding: atoms are even and ordered conjunctions are odd Cantor pairs
// (multiplied by two to avoid division).
total func PredicateAtomID(id nat) nat { return id*2 }
total func PredicateBothID(left nat, right nat) nat {
	return ((left+right)*(left+right+1)+right)*2+1
}

// Failure describes one failed atomic rule. Path uses dotted Go/JSON field
// notation and Code/Param retain machine-readable validation semantics.
type Failure struct {
	Path string
	Code string
	Param string
}

func (f Failure) Error() string {
	message := f.Code
	if f.Param != "" { message += "=" + f.Param }
	if f.Path == "" { return message }
	return f.Path + ": " + message
}

// Failures is stable in rule declaration order.
type Failures []Failure

func (failures Failures) Error() string {
	parts := make([]string, len(failures))
	for i, failure := range failures { parts[i] = failure.Error() }
	return strings.Join(parts, "; ")
}

type runner[T any] func(value T, path string, failures Failures) Failures

// Rule is an immutable executable witness for predicate p.
//goplus:derive off
type Rule[T any, p nat] enum {
	ruleValue(Predicate Predicate, Run runner[T]) Rule[T, p]
}

// Validated can only be constructed by this package after a rule succeeds.
//goplus:derive off
type Validated[T any, p nat] enum {
	validatedValue(Predicate Predicate, Value T, Rule Rule[T, p]) Validated[T, p]
}

// Outcome forces callers to handle validation failure explicitly.
//goplus:derive off
type Outcome[T any, p nat] enum {
	Accepted(Value Validated[T, p])
	Rejected(Failures Failures)
}

// Path is a typed field projection used to attach precise failure namespaces.
type Path[T any, V any] struct {
	Name string
	Get func(T) V
}

func makeRule[T any](0 p nat, predicate Predicate, run runner[T]) Rule[T, p] {
	return ruleValue(predicate, run)
}

func Field[T any, V any](name string, get func(T) V) Path[T, V] {
	if name == "" { panic("validate: empty field path") }
	if get == nil { panic("validate: nil field projection") }
	return Path[T, V]{Name: name, Get: get}
}

func joinPath(prefix string, field string) string {
	if prefix == "" { return field }
	if field == "" { return prefix }
	return prefix + "." + field
}

// Atom constructs an atomic predicate. IDs are application-owned stable
// non-negative integers and become part of the dependent result index.
func Atom[T any](id nat, code string, param string, check func(T) bool) Rule[T, PredicateAtomID(id)] {
	if id < 0 { panic("validate: negative predicate ID") }
	if code == "" { panic("validate: empty rule code") }
	if check == nil { panic("validate: nil rule check") }
	predicate := Named(int(id))
	run := func(value T, path string, failures Failures) Failures {
		if check(value) { return failures }
		return append(failures, Failure{Path: path, Code: code, Param: param})
	}
	return makeRule(PredicateAtomID(id), predicate, run)
}

// At lifts a value rule through a typed field projection without changing its
// proposition.
func At[T any, V any](0 p nat, path Path[T, V], rule Rule[V, p]) Rule[T, p] {
	match rule {
	case ruleValue(predicate, run):
		lifted := func(value T, prefix string, failures Failures) Failures {
			return run(path.Get(value), joinPath(prefix, path.Name), failures)
		}
		return ruleValue(predicate, lifted)
	}
}

// And forms conjunction and evaluates both sides in declaration order.
func And[T any](0 p nat, 0 q nat, left Rule[T, p], right Rule[T, q]) Rule[T, PredicateBothID(p, q)] {
	match left {
	case ruleValue(leftPredicate, leftRun):
		match right {
		case ruleValue(rightPredicate, rightRun):
			run := func(value T, path string, failures Failures) Failures {
				failures = leftRun(value, path, failures)
				return rightRun(value, path, failures)
			}
			return makeRule(PredicateBothID(p, q), Both(leftPredicate, rightPredicate), run)
		}
	}
}

// Validate executes rule and seals successful values with predicate p.
func Validate[T any](0 p nat, rule Rule[T, p], value T) Outcome[T, p] {
	match rule {
	case ruleValue(predicate, run):
		failures := run(value, "", nil)
		if len(failures) != 0 { return Rejected(failures) }
		return Accepted(validatedValue(predicate, value, rule))
	}
}

// Check is the direct diagnostic boundary analogous to tag validators' error
// return. Success returns nil without constructing a proof-bearing Outcome.
func Check[T any](0 p nat, rule Rule[T, p], value T) Failures {
	match rule {
	case ruleValue(_, run):
		return run(value, "", nil)
	}
}

// IsValid is the allocation-free boolean boundary for callers that do not need
// a witness or structured failures.
func IsValid[T any](0 p nat, rule Rule[T, p], value T) bool {
	match rule {
	case ruleValue(_, run):
		return len(run(value, "", nil)) == 0
	}
}

func Value[T any](0 p nat, value Validated[T, p]) T {
	match value {
	case validatedValue(_, raw, _):
		return raw
	}
}

func PredicateOfRule[T any](0 p nat, rule Rule[T, p]) Predicate {
	match rule {
	case ruleValue(predicate, _):
		return predicate
	}
}

func PredicateOf[T any](0 p nat, value Validated[T, p]) Predicate {
	match value {
	case validatedValue(predicate, _, _):
		return predicate
	}
}

func PredicateEqual(left Predicate, right Predicate) bool {
	match left {
	case Named(leftID):
		match right {
		case Named(rightID): return leftID == rightID
		case Both(_, _): return false
		}
	case Both(leftA, leftB):
		match right {
		case Named(_): return false
		case Both(rightA, rightB):
			return PredicateEqual(leftA, rightA) && PredicateEqual(leftB, rightB)
		}
	}
}

// Revalidate is statically same-predicate in Go+ and checks the retained witness
// so erased plain-Go callers cannot mix proofs from different rules.
func Revalidate[T any](0 p nat, rule Rule[T, p], value Validated[T, p]) bool {
	if !PredicateEqual(PredicateOfRule(rule), PredicateOf(value)) { return false }
	return IsValid(rule, Value(value))
}

// Map applies an arbitrary transformation and revalidates because ordinary Go
// functions are not proofs that p is preserved.
func Map[T any](0 p nat, value Validated[T, p], transform func(T) T) Outcome[T, p] {
	if transform == nil { panic("validate: nil transform") }
	match value {
	case validatedValue(_, raw, rule):
		return Validate(rule, transform(raw))
	}
}

func FailuresOf[T any](0 p nat, outcome Outcome[T, p]) Failures {
	match outcome {
	case Accepted(_): return nil
	case Rejected(failures): return failures
	}
}

// Error adapts a rule to conventional error-returning Go interfaces such as
// config.Validator while retaining Failures as the concrete error value.
func Error[T any](0 p nat, rule Rule[T, p], value T) error {
	failures := Check(rule, value)
	if len(failures) == 0 { return nil }
	return failures
}

type ConfigValidator[T any] struct { Rule Rule[T] }
func (validator ConfigValidator[T]) Validate(value T) error { return Error(validator.Rule, value) }
func AsConfigValidator[T any](0 p nat, rule Rule[T, p]) ConfigValidator[T] {
	return ConfigValidator[T]{Rule: rule}
}
