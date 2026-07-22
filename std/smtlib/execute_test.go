package smtlib

import (
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
