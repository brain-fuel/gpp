package smtlib

import (
	"strings"
	"testing"

	"goforge.dev/goplus/std/smt"
)

func TestExecuteBooleanModelAndValues(t *testing.T) {
	script := `(set-logic QF_BOOL)
(declare-const a Bool)
(declare-const b Bool)
(assert (or a b))
(assert (not a))
(check-sat)
(get-value (a b))
(get-model)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("check response=%T", result.Responses[5])
	}
	values := result.Responses[6].(ValuesAvailable).Values
	a := values[0].(BooleanValue)
	b := values[1].(BooleanValue)
	if a.Value || !b.Value {
		t.Fatalf("a=%v b=%v", a.Value, b.Value)
	}
	if _, ok := result.Responses[7].(ModelAvailable); !ok {
		t.Fatalf("model response=%T", result.Responses[7])
	}
}

func TestExecuteDifferenceLogicPushPop(t *testing.T) {
	script := `(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
(assert (<= (- x y) (- 1)))
(push 1)
(assert (<= (- y x) (- 1)))
(check-sat)
(pop 1)
(check-sat)
(get-value (x y))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[6].(Unsatisfiable); !ok {
		t.Fatalf("child check=%T", result.Responses[6])
	}
	if _, ok := result.Responses[8].(Satisfiable); !ok {
		t.Fatalf("parent check=%T", result.Responses[8])
	}
	values := result.Responses[9].(ValuesAvailable).Values
	if len(values) != 2 {
		t.Fatalf("values=%#v", values)
	}
}

func TestExecuteLinearIntegerArithmetic(t *testing.T) {
	script := `(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ x y) 10))
(assert (>= (+ (* 2 x) y) 11))
(check-sat)
(get-value (x y))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[5])
	}
	values, ok := result.Responses[6].(ValuesAvailable)
	if !ok || len(values.Values) != 2 {
		t.Fatalf("values=%#v", result.Responses[6])
	}

	unsat := `(set-logic QF_LIA)
(declare-const x Int)
(assert (= (* 2 x) 1))
(check-sat)`
	unsatResult := Execute(unsat).(Executed)
	if _, ok := unsatResult.Responses[3].(Unsatisfiable); !ok {
		t.Fatalf("integrality check=%T", unsatResult.Responses[3])
	}
}

func TestExecuteBooleanLinearIntegerArithmetic(t *testing.T) {
	script := `(set-logic QF_LIA)
(declare-const x Int)
(assert (or (= x 1) (= x 2)))
(assert (distinct x 1))
(assert (=> (= x 2) (> x 0)))
(check-sat)
(get-value (x))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[5])
	}
	values, ok := result.Responses[6].(ValuesAvailable)
	if !ok || len(values.Values) != 1 {
		t.Fatalf("values=%#v", result.Responses[6])
	}
	value, ok := values.Values[0].(IntegerValue)
	if !ok || value.Value != 2 {
		t.Fatalf("x=%#v", values.Values[0])
	}

	unsat := `(set-logic QF_LIA)
(declare-const x Int)
(assert (distinct x x))
(check-sat)`
	unsatResult := Execute(unsat).(Executed)
	if _, ok := unsatResult.Responses[3].(Unsatisfiable); !ok {
		t.Fatalf("distinct check=%T", unsatResult.Responses[3])
	}
}

func TestExecuteIntegerEuclideanDivisionAndModulo(t *testing.T) {
	script := `(set-logic QF_LIA)
(declare-const x Int)
(assert (= x (- 7)))
(assert (= (div x 3) (- 3)))
(assert (= (mod x 3) 2))
(check-sat)
(get-value ((div x 3) (mod x 3)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[5])
	}
	values, ok := result.Responses[6].(ValuesAvailable)
	if !ok || len(values.Values) != 2 {
		t.Fatalf("values=%#v", result.Responses[6])
	}
	quotient, quotientOK := values.Values[0].(IntegerValue)
	remainder, remainderOK := values.Values[1].(IntegerValue)
	if !quotientOK || quotient.Value != -3 || !remainderOK || remainder.Value != 2 {
		t.Fatalf("div/mod=%#v", values.Values)
	}
}

func TestExecuteIntegerDivisionWithNegativeConstantDivisor(t *testing.T) {
	script := `(set-logic QF_LIA)
(declare-const x Int)
(assert (= x (- 7)))
(assert (= (div x (- 3)) 3))
(assert (= (mod x (- 3)) 2))
(check-sat)
(get-value ((div x (- 3)) (mod x (- 3))))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[5])
	}
	values, ok := result.Responses[6].(ValuesAvailable)
	if !ok || len(values.Values) != 2 {
		t.Fatalf("values=%#v", result.Responses[6])
	}
	quotient, quotientOK := values.Values[0].(IntegerValue)
	remainder, remainderOK := values.Values[1].(IntegerValue)
	if !quotientOK || quotient.Value != 3 || !remainderOK || remainder.Value != 2 {
		t.Fatalf("div/mod=%#v", values.Values)
	}
}

func TestExecuteFiniteEnumerationDatatype(t *testing.T) {
	script := `(set-logic QF_DT)
(declare-datatype Color ((red) (green) (blue)))
(declare-const x Color)
(assert (not (= x red)))
(assert (is-green x))
(check-sat)
(get-value (x green (is-green x)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[5])
	}
	values, ok := result.Responses[6].(ValuesAvailable)
	if !ok || len(values.Values) != 3 {
		t.Fatalf("values=%#v", result.Responses[6])
	}
	x, xOK := values.Values[0].(DatatypeValue)
	green, greenOK := values.Values[1].(DatatypeValue)
	recognized, recognizedOK := values.Values[2].(BooleanValue)
	if !xOK || !greenOK || !recognizedOK || !recognized.Value || x.Value.ConstructorID != 1 || green.Value.ConstructorID != 1 || green.Value.ConstructorName != "green" {
		t.Fatalf("datatype values=%#v", values.Values)
	}
}

func TestExecuteFiniteEnumerationDatatypeExhaustion(t *testing.T) {
	script := `(set-logic QF_DT)
(declare-datatype Bit ((zero) (one)))
(declare-const a Bit)
(declare-const b Bit)
(declare-const c Bit)
(assert (distinct a b c))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[6].(Unsatisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[6])
	}
}

func TestExecuteRecursiveUnaryDatatype(t *testing.T) {
	script := `(set-logic QF_DT)
(declare-datatype Nat ((zero) (succ (pred Nat))))
(declare-const x Nat)
(assert (= x (succ (succ zero))))
(assert (= (pred x) (succ zero)))
(assert (is-succ x))
(check-sat)
(get-value (x (pred x) (is-succ x)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[6].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[6])
	}
	values, ok := result.Responses[7].(ValuesAvailable)
	if !ok || len(values.Values) != 3 {
		t.Fatalf("values=%#v", result.Responses[7])
	}
	x, xOK := values.Values[0].(DatatypeValue)
	pred, predOK := values.Values[1].(DatatypeValue)
	recognized, recognizedOK := values.Values[2].(BooleanValue)
	if !xOK || x.Value.ConstructorName != "succ" || x.Value.Child == nil || x.Value.Child.ConstructorName != "succ" || x.Value.Child.Child == nil || x.Value.Child.Child.ConstructorName != "zero" {
		t.Fatalf("x=%#v", values.Values[0])
	}
	if !predOK || pred.Value.ConstructorName != "succ" || pred.Value.Child == nil || pred.Value.Child.ConstructorName != "zero" {
		t.Fatalf("pred=%#v", values.Values[1])
	}
	if !recognizedOK || !recognized.Value {
		t.Fatalf("recognizer=%#v", values.Values[2])
	}
}

func TestExecuteRecursiveUnaryDatatypeAcyclicity(t *testing.T) {
	script := `(set-logic QF_DT)
(declare-datatype Nat ((zero) (succ (pred Nat))))
(declare-const x Nat)
(assert (= x (succ x)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[4].(Unsatisfiable); !ok {
		t.Fatalf("check=%T responses=%#v", result.Responses[4], result.Responses)
	}
}

func TestExecuteRecursiveUnaryDatatypeRecognizerModel(t *testing.T) {
	script := `(set-logic QF_DT)
(declare-datatype Nat ((zero) (succ (pred Nat))))
(declare-const x Nat)
(assert (is-succ x))
(check-sat)
(get-value (x))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	values, ok := result.Responses[5].(ValuesAvailable)
	if !ok || len(values.Values) != 1 {
		t.Fatalf("values=%#v", result.Responses[5])
	}
	value, ok := values.Values[0].(DatatypeValue)
	if !ok || value.Value.ConstructorName != "succ" || value.Value.Child == nil || value.Value.Child.ConstructorID != 0 {
		t.Fatalf("value=%#v", values.Values[0])
	}
}

func TestExecuteBinaryRecursiveDatatype(t *testing.T) {
	script := `(set-logic QF_DT)
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
(declare-const x Tree)
(assert (= x (node (node leaf leaf) leaf)))
(assert (= (left x) (node leaf leaf)))
(assert (is-node x))
(check-sat)
(get-value (x (left x) (right x)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[6].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[6])
	}
	values, ok := result.Responses[7].(ValuesAvailable)
	if !ok || len(values.Values) != 3 {
		t.Fatalf("values=%#v", result.Responses[7])
	}
	x, xOK := values.Values[0].(DatatypeValue)
	left, leftOK := values.Values[1].(DatatypeValue)
	right, rightOK := values.Values[2].(DatatypeValue)
	if !xOK || x.Value.ConstructorName != "node" || x.Value.Child == nil || x.Value.SecondChild == nil || x.Value.Child.ConstructorName != "node" || x.Value.SecondChild.ConstructorName != "leaf" {
		t.Fatalf("x=%#v", values.Values[0])
	}
	if !leftOK || left.Value.ConstructorName != "node" || left.Value.Child == nil || left.Value.SecondChild == nil || !rightOK || right.Value.ConstructorName != "leaf" {
		t.Fatalf("selectors=%#v", values.Values[1:])
	}
}

func TestExecuteBinaryRecursiveDatatypeAcyclicity(t *testing.T) {
	script := `(set-logic QF_DT)
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
(declare-const x Tree)
(assert (= x (node leaf x)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[4].(Unsatisfiable); !ok {
		t.Fatalf("check=%T responses=%#v", result.Responses[4], result.Responses)
	}
}

func TestExecuteNaryRecursiveDatatype(t *testing.T) {
	script := `(set-logic QF_DT)
(declare-datatype Tree ((leaf) (branch (first Tree) (second Tree) (third Tree))))
(declare-const x Tree)
(assert (= x (branch leaf (branch leaf leaf leaf) leaf)))
(assert (= (second x) (branch leaf leaf leaf)))
(assert (is-branch x))
(check-sat)
(get-value (x (first x) (second x) (third x)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[6].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[6])
	}
	values, ok := result.Responses[7].(ValuesAvailable)
	if !ok || len(values.Values) != 4 {
		t.Fatalf("values=%#v", result.Responses[7])
	}
	x, xOK := values.Values[0].(DatatypeValue)
	second, secondOK := values.Values[2].(DatatypeValue)
	xSecond, xSecondOK := x.Value.Children.At(1)
	if !xOK || x.Value.ConstructorName != "branch" || x.Value.Children.Len() != 3 || !xSecondOK || xSecond.ConstructorName != "branch" || !secondOK || second.Value.ConstructorName != "branch" || second.Value.Children.Len() != 3 {
		t.Fatalf("n-ary values=%#v", values.Values)
	}
}

func TestExecuteNaryRecursiveDatatypeAcyclicity(t *testing.T) {
	script := `(set-logic QF_DT)
(declare-datatype Tree ((leaf) (branch (first Tree) (second Tree) (third Tree))))
(declare-const x Tree)
(assert (= x (branch leaf leaf x)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[4].(Unsatisfiable); !ok {
		t.Fatalf("check=%T responses=%#v", result.Responses[4], result.Responses)
	}
}

func TestExecuteMixedSortRecursiveDatatype(t *testing.T) {
	script := `(set-logic ALL)
(declare-datatype Tree ((leaf) (node (flag Bool) (payload Int) (weight Real) (bits (_ BitVec 8)) (next Tree))))
(declare-const x Tree)
(assert (= x (node true 42 (/ 3.0 2.0) #xa5 leaf)))
(assert (= (payload x) 42))
(assert (= (next x) leaf))
(assert (is-node x))
(check-sat)
(get-value (x (flag x) (payload x) (weight x) (bits x) (next x)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[7].(Satisfiable); !ok {
		t.Fatalf("check=%T responses=%#v", result.Responses[7], result.Responses)
	}
	values, ok := result.Responses[8].(ValuesAvailable)
	if !ok || len(values.Values) != 6 {
		t.Fatalf("values=%#v", result.Responses[8])
	}
	x, xOK := values.Values[0].(DatatypeValue)
	if !xOK || x.Value.ConstructorName != "node" || x.Value.Fields.Len() != 5 {
		t.Fatalf("x=%#v", values.Values[0])
	}
	payload, _ := x.Value.Fields.At(1)
	weight, _ := x.Value.Fields.At(2)
	bits, _ := x.Value.Fields.At(3)
	next, _ := x.Value.Fields.At(4)
	if smt.CompareIntegerValue(payload.Integer, smt.NewIntegerValue(42)) != 0 || smt.CompareRational(weight.Real, smt.NewRational(3, 2)) != 0 || !smt.EqualBitVectorValue(bits.BitVector, smt.NewBitVectorUint64(8, 0xa5)) || next.Datatype == nil || next.Datatype.ConstructorName != "leaf" {
		t.Fatalf("fields=%+v", x.Value.Fields)
	}
}

func TestExecuteMixedSortDatatypeInjectivity(t *testing.T) {
	script := `(declare-datatype Box ((box (payload Int))))
(assert (= (box 1) (box 2)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[2].(Unsatisfiable); !ok {
		t.Fatalf("check=%T responses=%#v", result.Responses[2], result.Responses)
	}
}

func TestExecuteMixedSortRecognizerSelectorModel(t *testing.T) {
	script := `(declare-datatype Box ((box (payload Int))))
(declare-const x Box)
(assert (is-box x))
(assert (= (payload x) 7))
(check-sat)
(get-value (x))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[4].(Satisfiable); !ok {
		t.Fatalf("check=%T responses=%#v", result.Responses[4], result.Responses)
	}
	values := result.Responses[5].(ValuesAvailable)
	x := values.Values[0].(DatatypeValue)
	payload, payloadOK := x.Value.Fields.At(0)
	if !payloadOK || smt.CompareIntegerValue(payload.Integer, smt.NewIntegerValue(7)) != 0 {
		t.Fatalf("recognizer-only mixed model=%+v", x.Value)
	}
}

func TestExecuteMutuallyRecursiveDatatypes(t *testing.T) {
	script := `(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf) (node (children Forest)))
   ((nil) (cons (head Tree) (tail Forest)))))
(declare-const x Tree)
(assert (= x (node (cons leaf nil))))
(assert (= (head (children x)) leaf))
(assert (= (tail (children x)) nil))
(assert (is-node x))
(check-sat)
(get-value (x (children x)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[6].(Satisfiable); !ok {
		t.Fatalf("check=%T responses=%#v", result.Responses[6], result.Responses)
	}
	values := result.Responses[7].(ValuesAvailable)
	tree := values.Values[0].(DatatypeValue)
	forest := values.Values[1].(DatatypeValue)
	children, childrenOK := tree.Value.Fields.At(0)
	head, headOK := forest.Value.Fields.At(0)
	tail, tailOK := forest.Value.Fields.At(1)
	if !childrenOK || children.Datatype == nil || children.Datatype.ConstructorName != "cons" || !headOK || head.Datatype == nil || head.Datatype.ConstructorName != "leaf" || !tailOK || tail.Datatype == nil || tail.Datatype.ConstructorName != "nil" {
		t.Fatalf("mutual values=%#v", values.Values)
	}
}

func TestExecuteMutuallyRecursiveDatatypeCycle(t *testing.T) {
	script := `(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf) (node (children Forest)))
   ((nil) (cons (head Tree) (tail Forest)))))
(declare-const tree Tree)
(declare-const forest Forest)
(assert (= tree (node forest)))
(assert (= forest (cons tree nil)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Unsatisfiable); !ok {
		t.Fatalf("check=%T responses=%#v", result.Responses[5], result.Responses)
	}
}

func TestExecuteMutuallyRecursiveRecognizerModel(t *testing.T) {
	script := `(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf) (node (children Forest)))
   ((nil) (cons (head Tree) (tail Forest)))))
(declare-const x Tree)
(assert (is-node x))
(check-sat)
(get-value (x))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[3].(Satisfiable); !ok {
		t.Fatalf("check=%T responses=%#v", result.Responses[3], result.Responses)
	}
	value := result.Responses[4].(ValuesAvailable).Values[0].(DatatypeValue).Value
	children, childrenOK := value.Fields.At(0)
	if value.ConstructorName != "node" || !childrenOK || children.Datatype == nil || children.Datatype.DatatypeID == value.DatatypeID || children.Datatype.ConstructorID != 0 {
		t.Fatalf("mutual recognizer model=%+v", value)
	}
}

func TestExecuteMutuallyRecursiveDatatypeProductivity(t *testing.T) {
	product := `(declare-datatypes ((Box 0)) (((box (payload Int)))))
(declare-const x Box)
(assert (= x (box 7)))
(check-sat)`
	result, ok := Execute(product).(Executed)
	if !ok {
		t.Fatalf("productive scalar datatype result=%#v", Execute(product))
	}
	if _, ok := result.Responses[3].(Satisfiable); !ok {
		t.Fatalf("productive scalar datatype check=%#v", result.Responses)
	}
	uninhabited := `(declare-datatypes ((A 0) (B 0)) (((a (to-b B))) ((b (to-a A)))))`
	failed, ok := Execute(uninhabited).(ExecutionFailed)
	if !ok || len(failed.Errors) != 1 || !strings.Contains(failed.Errors[0].Message, "uninhabited sort") {
		t.Fatalf("uninhabited mutual datatype result=%#v", Execute(uninhabited))
	}
}

func TestExecuteUnaryParametricDatatype(t *testing.T) {
	script := `(declare-datatypes ((PList 1))
	  ((par (T) ((nil) (cons (head T) (tail (PList T)))))))
	(declare-const xs (PList Int))
	(assert (= xs (cons 1 (as nil (PList Int)))))
	(assert (= (head xs) 1))
	(assert ((_ is cons) xs))
	(check-sat)
	(get-value (xs (head xs) (tail xs)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("expected sat, got %#v", result.Responses[5])
	}
	values := result.Responses[6].(ValuesAvailable).Values
	xValue, xOK := values[0].(DatatypeValue)
	headValue, headOK := values[1].(IntegerValue)
	tailValue, tailOK := values[2].(DatatypeValue)
	if !xOK || !headOK || !tailOK {
		t.Fatalf("unexpected parametric values: %#v", values)
	}
	x, head, tail := xValue.Value, headValue.Value, tailValue.Value
	if x.ConstructorName != "cons" || head != 1 || tail.ConstructorName != "nil" {
		t.Fatalf("unexpected parametric model: x=%#v head=%#v tail=%#v", x, head, tail)
	}
}

func TestExecuteDistinctParametricDatatypeInstances(t *testing.T) {
	script := `(declare-datatypes ((Box 1))
	  ((par (T) ((box (value T))))))
	(declare-const i (Box Int))
	(declare-const b (Box Bool))
	(assert (= i (box 7)))
	(assert (= b (box true)))
	(check-sat)
	(get-value ((value i) (value b)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("expected sat, got %#v", result.Responses[5])
	}
	values := result.Responses[6].(ValuesAvailable).Values
	if integer, ok := values[0].(IntegerValue); !ok || integer.Value != 7 {
		t.Fatalf("unexpected integer box value: %#v", values[0])
	}
	if boolean, ok := values[1].(BooleanValue); !ok || !boolean.Value {
		t.Fatalf("unexpected Boolean box value: %#v", values[1])
	}
}

func TestExecuteParametricDatatypeAcrossSupportedSorts(t *testing.T) {
	script := `(declare-datatype Color ((red) (blue)))
	(declare-datatypes ((Box 1)) ((par (T) ((box (value T))))))
	(declare-const r (Box Real))
	(declare-const v (Box (_ BitVec 8)))
	(declare-const c (Box Color))
	(assert (= r (box (/ 3 2))))
	(assert (= v (box #xa5)))
	(assert (= c (box red)))
	(check-sat)
	(get-value ((value r) (value v) (value c)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[8].(Satisfiable); !ok {
		t.Fatalf("expected sat, got %#v", result.Responses[8])
	}
	values := result.Responses[9].(ValuesAvailable).Values
	real, realOK := values[0].(RationalValue)
	bits, bitsOK := values[1].(BitVectorValue)
	color, colorOK := values[2].(DatatypeValue)
	if !realOK || smt.CompareRational(real.Value, smt.NewRational(3, 2)) != 0 || !bitsOK || !smt.EqualBitVectorValue(bits.Value, smt.NewBitVectorUint64(8, 0xa5)) || !colorOK || color.Value.ConstructorName != "red" {
		t.Fatalf("unexpected cross-sort parametric values: %#v", values)
	}
}

func TestExecuteNestedParametricDatatypeInstantiation(t *testing.T) {
	script := `(declare-datatypes ((PList 1))
	  ((par (T) ((nil) (cons (head T) (tail (PList T)))))))
	(declare-datatypes ((Box 1)) ((par (T) ((box (value T))))))
	(declare-const nested (Box (PList Int)))
	(assert (= nested (box (cons 9 (as nil (PList Int))))))
	(assert (= (head (value nested)) 9))
	(check-sat)
	(get-value ((value nested) (head (value nested))))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("expected sat, got %#v", result.Responses[5])
	}
	values := result.Responses[6].(ValuesAvailable).Values
	list, listOK := values[0].(DatatypeValue)
	head, headOK := values[1].(IntegerValue)
	if !listOK || list.Value.ConstructorName != "cons" || !headOK || head.Value != 9 {
		t.Fatalf("unexpected nested parametric values: %#v", values)
	}
}

func TestExecuteRejectsInvalidParametricDatatypeInstances(t *testing.T) {
	uninhabited := `(declare-datatypes ((Loop 1))
	  ((par (T) ((loop (next (Loop T)))))))
	(declare-const x (Loop Int))`
	failed, ok := Execute(uninhabited).(ExecutionFailed)
	if !ok || len(failed.Errors) != 1 || !strings.Contains(failed.Errors[0].Message, "uninhabited") {
		t.Fatalf("uninhabited parametric datatype result=%#v", Execute(uninhabited))
	}

	duplicate := `(declare-datatypes ((Pair 1))
	  ((par (T) ((pair (item T) (item T))))))
	(declare-const x (Pair Int))`
	failed, ok = Execute(duplicate).(ExecutionFailed)
	if !ok || len(failed.Errors) != 1 || !strings.Contains(failed.Errors[0].Message, "duplicate datatype selector") {
		t.Fatalf("duplicate parametric selector result=%#v", Execute(duplicate))
	}
}

func TestExecuteParametricDatatypeMatch(t *testing.T) {
	script := `(declare-datatypes ((PList 1))
	  ((par (T) ((nil) (cons (head T) (tail (PList T)))))))
	(declare-const xs (PList Int))
	(assert (= xs (cons 42 (as nil (PList Int)))))
	(assert (= (match xs (((nil) 0) ((cons h t) h))) 42))
	(check-sat)
	(get-value ((match xs (((nil) 0) ((cons h t) h)))))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[4].(Satisfiable); !ok {
		t.Fatalf("expected sat, got %#v", result.Responses[4])
	}
	value, ok := result.Responses[5].(ValuesAvailable).Values[0].(IntegerValue)
	if !ok || value.Value != 42 {
		t.Fatalf("unexpected match value: %#v", result.Responses[5])
	}
}

func TestExecuteUnconstrainedParametricDatatypeMatch(t *testing.T) {
	script := `(declare-datatypes ((PList 1))
	  ((par (T) ((nil) (cons (head T) (tail (PList T)))))))
	(declare-const xs (PList Int))
	(assert (= (match xs (((nil) 0) ((cons h t) h))) 42))
	(check-sat)
	(get-value (xs (match xs (((nil) 0) ((cons h t) h)))))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[3].(Satisfiable); !ok {
		t.Fatalf("expected sat, got %#v", result.Responses[3])
	}
	values := result.Responses[4].(ValuesAvailable).Values
	list, listOK := values[0].(DatatypeValue)
	matched, matchOK := values[1].(IntegerValue)
	if !listOK || list.Value.ConstructorName != "cons" || !matchOK || matched.Value != 42 {
		t.Fatalf("unexpected unconstrained match values: %#v", values)
	}
}

func TestExecuteRejectsNonExhaustiveParametricDatatypeMatch(t *testing.T) {
	script := `(declare-datatypes ((PList 1))
	  ((par (T) ((nil) (cons (head T) (tail (PList T)))))))
	(declare-const xs (PList Int))
	(assert (= (match xs (((nil) 0))) 0))`
	failed, ok := Execute(script).(ExecutionFailed)
	if !ok || len(failed.Errors) != 1 || !strings.Contains(failed.Errors[0].Message, "non-exhaustive") {
		t.Fatalf("non-exhaustive match result=%#v", Execute(script))
	}
}

func TestExecuteParametricDatatypeUpdateField(t *testing.T) {
	script := `(declare-datatypes ((PList 1))
	  ((par (T) ((nil) (cons (head T) (tail (PList T)))))))
	(declare-const xs (PList Int))
	(assert (= xs (cons 42 (as nil (PList Int)))))
	(assert (= ((_ update-field head) xs 7) (cons 7 (as nil (PList Int)))))
	(assert (= ((_ update-field head) (as nil (PList Int)) 9) (as nil (PList Int))))
	(check-sat)
	(get-value (((_ update-field head) xs 7)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[5].(Satisfiable); !ok {
		t.Fatalf("expected sat, got %#v", result.Responses[5])
	}
	value, ok := result.Responses[6].(ValuesAvailable).Values[0].(DatatypeValue)
	field, fieldOK := value.Value.Fields.At(0)
	integer, integerOK := field.Integer.Int64()
	if !ok || value.Value.ConstructorName != "cons" || !fieldOK || !integerOK || integer != 7 {
		t.Fatalf("unexpected update-field value: %#v", result.Responses[6])
	}
}

func TestExecuteSymbolicParametricDatatypeUpdateField(t *testing.T) {
	script := `(declare-datatypes ((PList 1))
	  ((par (T) ((nil) (cons (head T) (tail (PList T)))))))
	(declare-const xs (PList Int))
	(assert ((_ is cons) xs))
	(assert (= (head ((_ update-field head) xs 13)) 13))
	(check-sat)
	(get-value (((_ update-field head) xs 13)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[4].(Satisfiable); !ok {
		t.Fatalf("expected sat, got %#v", result.Responses[4])
	}
	value, ok := result.Responses[5].(ValuesAvailable).Values[0].(DatatypeValue)
	field, fieldOK := value.Value.Fields.At(0)
	integer, integerOK := field.Integer.Int64()
	if !ok || value.Value.ConstructorName != "cons" || !fieldOK || !integerOK || integer != 13 {
		t.Fatalf("unexpected symbolic update-field value: %#v", result.Responses[5])
	}
}

func TestExecuteAssumptionCore(t *testing.T) {
	script := `(declare-const a Bool)
(declare-const b Bool)
(assert (or a b))
(check-sat-assuming ((not a) (not b) true))`
	result := Execute(script).(Executed)
	core, ok := result.Responses[3].(AssumptionsUnsatisfiable)
	if !ok {
		t.Fatalf("response=%T", result.Responses[3])
	}
	if len(core.Indices) != 2 || core.Indices[0] != 0 || core.Indices[1] != 1 {
		t.Fatalf("core=%v", core.Indices)
	}
}

func TestExecuteGroundEUFCongruence(t *testing.T) {
	script := `(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[7].(Unsatisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[7])
	}
}

func TestExecuteGroundBinaryEUFCongruence(t *testing.T) {
	source := `(set-logic QF_UF)
(declare-sort A 0)
(declare-sort B 0)
(declare-sort R 0)
(declare-const a A)
(declare-const a2 A)
(declare-const b B)
(declare-const b2 B)
(declare-fun combine (A B) R)
(assert (= a a2))
(assert (= b b2))
(assert (not (= (combine a b) (combine a2 b2))))
(check-sat)`
	result, ok := Execute(source).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(source))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%T", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteDisjointEUFLinearRealCombination(t *testing.T) {
	source := `(set-logic ALL)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)
(declare-const x Real)
(assert (not (= a b)))
(assert (= (f a) (f b)))
(assert (<= 1 x))
(assert (<= x 2))
(check-sat)
(get-value (x))`
	result, ok := Execute(source).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(source))
	}
	if _, ok := result.Responses[10].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[10])
	}
	value, ok := result.Responses[11].(ValuesAvailable).Values[0].(RationalValue)
	if !ok || value.Value.Sign() <= 0 {
		t.Fatalf("value=%#v", result.Responses[11])
	}
}

func TestExecuteRealSortedFunctionCongruenceAndSharedBoundary(t *testing.T) {
	congruence := `(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun f (Real) Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)`
	result, ok := Execute(congruence).(Executed)
	if !ok {
		t.Fatalf("congruence=%#v", Execute(congruence))
	}
	if _, ok := result.Responses[6].(Unsatisfiable); !ok {
		t.Fatalf("congruence check=%T", result.Responses[6])
	}

	shared := `(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun f (Real) Real)
(assert (<= x y))
(assert (<= y x))
(assert (not (= (f x) (f y))))
(check-sat)`
	result, ok = Execute(shared).(Executed)
	if !ok {
		t.Fatalf("shared=%#v", Execute(shared))
	}
	if _, ok := result.Responses[7].(Unsatisfiable); !ok {
		t.Fatalf("shared check=%T", result.Responses[7])
	}
}

func TestExecutePurifiedRealFunctionArithmetic(t *testing.T) {
	source := `(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun f (Real) Real)
(assert (= x y))
(assert (<= (f x) 0))
(assert (< 0 (f y)))
(check-sat)`
	result, ok := Execute(source).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(source))
	}
	if _, ok := result.Responses[7].(Unsatisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[7])
	}
}

func TestExecutePurifiedBinaryRealFunctionArithmetic(t *testing.T) {
	script := `(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun combine (Real Real) Real)
(assert (= x y))
(assert (<= (combine (+ x 1) y) 0))
(assert (< 0 (combine (+ y 1) x)))
(check-sat)`
	result := Execute(script)
	executed, ok := result.(Executed)
	if !ok {
		t.Fatalf("execute=%#v", result)
	}
	if _, ok := executed.Responses[len(executed.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%#v", executed.Responses[len(executed.Responses)-1])
	}
}

func TestExecuteIndexedBitVectorArithmetic(t *testing.T) {
	script := `(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #xa5))
(assert (not (= (bvand x #x0f) #x05)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%#v", result.Responses[len(result.Responses)-1])
	}

	wrap := `(set-logic QF_BV)
(assert (not (= (bvadd #xff #x01) #x00)))
(check-sat)`
	result, ok = Execute(wrap).(Executed)
	if !ok {
		t.Fatalf("wrap=%#v", Execute(wrap))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("wrap response=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteBitVectorOrdering(t *testing.T) {
	script := `(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x7f))
(assert (not (bvult x #x80)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%#v", result.Responses[len(result.Responses)-1])
	}
	signed := `(set-logic QF_BV)
(assert (not (bvslt #xff #x00)))
(check-sat)`
	result, ok = Execute(signed).(Executed)
	if !ok {
		t.Fatalf("signed=%#v", Execute(signed))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("signed response=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteBitVectorSubtractionAndMultiplication(t *testing.T) {
	script := `(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x0d))
(assert (not (= (bvmul x #x07) #x5b)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%#v", result.Responses[len(result.Responses)-1])
	}
	underflow := `(set-logic QF_BV)
(assert (not (= (bvsub #x00 #x01) #xff)))
(check-sat)`
	result, ok = Execute(underflow).(Executed)
	if !ok {
		t.Fatalf("underflow=%#v", Execute(underflow))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("underflow response=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteBitVectorShifts(t *testing.T) {
	script := `(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x81))
(assert (not (= (bvlshr x #x04) #x08)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%#v", result.Responses[len(result.Responses)-1])
	}
	boundary := `(set-logic QF_BV)
(assert (not (= (bvashr #x80 #x09) #xff)))
(check-sat)`
	result, ok = Execute(boundary).(Executed)
	if !ok {
		t.Fatalf("boundary=%#v", Execute(boundary))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("boundary response=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteBitVectorDivisionAndRemainder(t *testing.T) {
	script := `(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x64))
(assert (not (= (bvudiv x #x07) #x0e)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%#v", result.Responses[len(result.Responses)-1])
	}
	corner := `(set-logic QF_BV)
(assert (not (= (bvsdiv #x80 #x00) #x01)))
(assert (not (= (bvurem #x64 #x00) #x64)))
(check-sat)`
	result, ok = Execute(corner).(Executed)
	if !ok {
		t.Fatalf("corner=%#v", Execute(corner))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("corner response=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteBitVectorStructuralOperators(t *testing.T) {
	script := `(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #xab))
(assert (not (= ((_ extract 7 4) x) #xa)))
(assert (not (= (concat #xa #xb) #xab)))
(assert (not (= ((_ zero_extend 8) #xff) #x00ff)))
(assert (not (= ((_ sign_extend 8) #xff) #xffff)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteBitVectorIntegerConversions(t *testing.T) {
	script := `(set-logic ALL)
(declare-const x (_ BitVec 8))
(assert (= x #xff))
(assert (= (ubv_to_int x) 255))
(assert (= (sbv_to_int x) (- 1)))
(assert (= ((_ int_to_bv 8) (- 129)) #x7f))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Satisfiable); !ok {
		t.Fatalf("last response=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteGroundIntegerArrayReadOverWrite(t *testing.T) {
	script := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(assert (= (select (store a 7 42) 7) 42))
(assert (= (select ((as const (Array Int Int)) 11) 123) 11))
(assert (not (= (select (store a 7 42) 7) 42)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteGroundBitVectorArrayReadOverWrite(t *testing.T) {
	script := `(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= (select (store a #x3 #xa5) #x3) #xa5))
(assert (= (select ((as const (Array (_ BitVec 4) (_ BitVec 8))) #x11) #xf) #x11))
(assert (not (= (select (store a #x3 #xa5) #x3) #xa5)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last response=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteGroundBitVectorArrayCongruence(t *testing.T) {
	script := `(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= a b))
(assert (not (= (select a #x7) (select b #x7))))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteGroundBitVectorArrayDisequality(t *testing.T) {
	for name, script := range map[string]string{
		"distinct-satisfiable": `(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
(assert (not (= a b)))
(check-sat)`,
		"equal-and-distinct": `(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= a b))
(assert (not (= a b)))
(check-sat)`,
	} {
		t.Run(name, func(t *testing.T) {
			result, ok := Execute(script).(Executed)
			if !ok {
				t.Fatalf("execute=%#v", Execute(script))
			}
			last := result.Responses[len(result.Responses)-1]
			if name == "distinct-satisfiable" {
				if _, ok := last.(Satisfiable); !ok {
					t.Fatalf("last=%#v", last)
				}
			} else if _, ok := last.(Unsatisfiable); !ok {
				t.Fatalf("last=%#v", last)
			}
		})
	}
}

func TestExecuteGroundBitVectorArrayStoreExtensionality(t *testing.T) {
	for name, assertion := range map[string]string{
		"commuting": `(not (= (store (store a #x3 #x01) #x4 #x02)
                         (store (store a #x4 #x02) #x3 #x01)))`,
		"overwrite": `(not (= (store (store a #x3 #x01) #x3 #x02)
                        (store a #x3 #x02)))`,
		"different": `(not (= (store a #x3 #x01) (store a #x3 #x02)))`,
	} {
		t.Run(name, func(t *testing.T) {
			script := `(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(assert ` + assertion + `)
(check-sat)`
			result, ok := Execute(script).(Executed)
			if !ok {
				t.Fatalf("execute=%#v", Execute(script))
			}
			last := result.Responses[len(result.Responses)-1]
			if name == "different" {
				if _, ok := last.(Satisfiable); !ok {
					t.Fatalf("last=%#v", last)
				}
			} else if _, ok := last.(Unsatisfiable); !ok {
				t.Fatalf("last=%#v", last)
			}
		})
	}
}

func TestExecuteGroundBitVectorArrayModelValues(t *testing.T) {
	script := `(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
(assert (not (= a b)))
(check-sat)
(get-value ((select a #x0) (select b #x0) (select (store a #x3 #xa5) #x3)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	values, ok := result.Responses[len(result.Responses)-1].(ValuesAvailable)
	if !ok || len(values.Values) != 3 {
		t.Fatalf("last=%#v", result.Responses[len(result.Responses)-1])
	}
	left := values.Values[0].(BitVectorValue).Value
	right := values.Values[1].(BitVectorValue).Value
	stored := values.Values[2].(BitVectorValue).Value
	if smt.EqualBitVectorValue(left, right) {
		t.Fatalf("missing extensional witness: left=%#v right=%#v", left, right)
	}
	if !smt.EqualBitVectorValue(stored, smt.NewBitVectorUint64(8, 0xa5)) {
		t.Fatalf("stored=%#v", stored)
	}
}

func TestExecuteGroundBitVectorArraySymbolicIndex(t *testing.T) {
	script := `(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(declare-const j (_ BitVec 4))
(assert (= i j))
(assert (not (= (select (store a i #xa5) j) #xa5)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteGroundIntegerArrayCongruence(t *testing.T) {
	script := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (= a b))
(assert (not (= (select a 7) (select b 7))))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteGroundIntegerArraySymbolicIndex(t *testing.T) {
	script := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (= i j))
(assert (not (= (select (store a i 42) j) 42)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last=%#v", result.Responses[len(result.Responses)-1])
	}
}

func TestExecuteGroundIntegerArrayModelValues(t *testing.T) {
	script := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (not (= a b)))
(assert (= (select a 7) 42))
(check-sat)
(get-value ((select a 7) (select a 8) (select b 8)))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-2].(Satisfiable); !ok {
		t.Fatalf("check=%#v", result.Responses[len(result.Responses)-2])
	}
	values := result.Responses[len(result.Responses)-1].(ValuesAvailable).Values
	aSeven := values[0].(IntegerValue).Value
	aEight := values[1].(IntegerValue).Value
	bEight := values[2].(IntegerValue).Value
	if aSeven != 42 || aEight == bEight {
		t.Fatalf("a[7]=%d a[8]=%d b[8]=%d", aSeven, aEight, bEight)
	}
}

func TestExecuteGroundIntegerArrayStoreExtensionality(t *testing.T) {
	script := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(assert (= (store a 7 (select a 7)) a))
(assert (not (= (store (store a 7 1) 8 2) (store (store a 8 2) 7 1))))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last=%#v", result.Responses[len(result.Responses)-1])
	}

	satisfiable := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(assert (not (= (store a 7 1) (store a 7 2))))
(check-sat)`
	second, ok := Execute(satisfiable).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(satisfiable))
	}
	if _, ok := second.Responses[len(second.Responses)-1].(Satisfiable); !ok {
		t.Fatalf("last=%#v", second.Responses[len(second.Responses)-1])
	}
}

func TestExecuteGroundIntegerArrayCrossBaseStoreEquality(t *testing.T) {
	script := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (= (store a 7 1) (store b 7 1)))
(assert (not (= (select a 8) (select b 8))))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last=%#v", result.Responses[len(result.Responses)-1])
	}

	overwritten := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (= (store a 7 1) (store b 7 1)))
(assert (= (select a 7) 2))
(assert (= (select b 7) 3))
(check-sat)
(get-value ((select a 8) (select b 8)))`
	second, ok := Execute(overwritten).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(overwritten))
	}
	if _, ok := second.Responses[len(second.Responses)-2].(Satisfiable); !ok {
		t.Fatalf("check=%#v", second.Responses[len(second.Responses)-2])
	}
	values := second.Responses[len(second.Responses)-1].(ValuesAvailable).Values
	if values[0].(IntegerValue).Value != values[1].(IntegerValue).Value {
		t.Fatalf("outside model=%#v", values)
	}
}

func TestExecuteGroundIntegerArrayConstantBaseEquality(t *testing.T) {
	script := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(assert (= a ((as const (Array Int Int)) 0)))
(assert (not (= (select a 8) 0)))
(check-sat)`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(script))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last=%#v", result.Responses[len(result.Responses)-1])
	}

	overwritten := `(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(assert (= (store a 7 0) (store ((as const (Array Int Int)) 0) 7 0)))
(assert (= (select a 7) 5))
(check-sat)
(get-value ((select a 8)))`
	second, ok := Execute(overwritten).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(overwritten))
	}
	if _, ok := second.Responses[len(second.Responses)-2].(Satisfiable); !ok {
		t.Fatalf("check=%#v", second.Responses[len(second.Responses)-2])
	}
	value := second.Responses[len(second.Responses)-1].(ValuesAvailable).Values[0].(IntegerValue)
	if value.Value != 0 {
		t.Fatalf("model=%#v", value)
	}
}

func TestExecuteMixedArrayArithmetic(t *testing.T) {
	shared := `(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (<= i j))
(assert (<= j i))
(assert (not (= (select (store a i 42) j) 42)))
(check-sat)`
	result, ok := Execute(shared).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(shared))
	}
	if _, ok := result.Responses[len(result.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last=%#v", result.Responses[len(result.Responses)-1])
	}

	disjoint := `(set-logic QF_AUFBV)
(declare-const a (Array Int Int))
(assert (= (select (store a 7 42) 7) 42))
(assert (not (= #xa5 #xa5)))
(check-sat)`
	second, ok := Execute(disjoint).(Executed)
	if !ok {
		t.Fatalf("execute=%#v", Execute(disjoint))
	}
	if _, ok := second.Responses[len(second.Responses)-1].(Unsatisfiable); !ok {
		t.Fatalf("last=%#v", second.Responses[len(second.Responses)-1])
	}
}

func TestExecuteExactLinearRealArithmetic(t *testing.T) {
	script := `(set-logic QF_LRA)
(declare-const x Real)
(assert (<= (+ (* 2 x) (/ 1 3)) 3.5))
(assert (< 0 x))
(check-sat)
(get-value (x))`
	result, ok := Execute(script).(Executed)
	if !ok {
		t.Fatalf("result=%#v", Execute(script))
	}
	if _, ok := result.Responses[4].(Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[4])
	}
	value, ok := result.Responses[5].(ValuesAvailable).Values[0].(RationalValue)
	if !ok || value.Value.Sign() <= 0 {
		t.Fatalf("value=%#v", result.Responses[5])
	}
}

func TestExecuteStrictLinearRealContradiction(t *testing.T) {
	script := `(set-logic QF_LRA)
(declare-const x Real)
(assert (< x 0))
(assert (<= 0 x))
(check-sat)`
	result := Execute(script).(Executed)
	if _, ok := result.Responses[4].(Unsatisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[4])
	}
}

func TestExecuteRejectsUnsupportedTermAndScope(t *testing.T) {
	for _, script := range []string{
		`(declare-const x Int) (assert (= (* x x) 4))`,
		`(pop 1)`,
	} {
		result, ok := Execute(script).(ExecutionFailed)
		if !ok || len(result.Errors) == 0 {
			t.Fatalf("script=%q result=%#v", script, Execute(script))
		}
	}
}

var benchmarkExecutionResult ExecutionResult

func BenchmarkExecuteBoolean(b *testing.B) {
	const script = `(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(assert (or a b))
(assert (not a))
(check-sat)
(get-value (a b))`
	b.ReportAllocs()
	for b.Loop() {
		benchmarkExecutionResult = Execute(script)
	}
}

func BenchmarkExecuteDifferenceLogic(b *testing.B) {
	const script = `(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
(assert (<= (- x y) 3))
(assert (<= y 2))
(assert (<= 4 x))
(check-sat)
(get-value (x y))`
	b.ReportAllocs()
	for b.Loop() {
		benchmarkExecutionResult = Execute(script)
	}
}
