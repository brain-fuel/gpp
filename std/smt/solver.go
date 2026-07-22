package smt

import "sync"

// BooleanConjunction is a compact conjunction with per-item polarity. It lets
// compatibility layers fuse Not/And construction while preserving ordinary
// Boolean semantics for every solver backend.
type BooleanConjunction struct {
	Count           int
	InlineTerms     [4]Term[BoolSort]
	InlineNegated   [4]bool
	OverflowTerms   []Term[BoolSort]
	OverflowNegated []bool
}

func (BooleanConjunction) isTerm(BoolSort) {}

func (conjunction BooleanConjunction) values() ([]Term[BoolSort], []bool) {
	if conjunction.OverflowTerms != nil {
		return conjunction.OverflowTerms[:conjunction.Count], conjunction.OverflowNegated[:conjunction.Count]
	}
	return conjunction.InlineTerms[:conjunction.Count], conjunction.InlineNegated[:conjunction.Count]
}

const (
	checkUnknown = iota
	checkSat
	checkUnsat
)

type engine struct {
	inlineAssertions [4]Term[BoolSort]
	assertions       []Term[BoolSort]
	checkOnce        sync.Once
	result           checkOutcome
	publicOnce       sync.Once
	publicResult     CheckResult
	publicContext    int
	adapterOnce      sync.Once
	adapterKey       any
	adapterValue     any
}

// MemoizedView lets a compatibility layer derive one immutable result view
// without maintaining a second heap-resident cache. key must be a
// package-unique comparable value and remains fixed for this solver state.
func MemoizedView(solver Solver, key any, build func(CheckResult) any) any {
	state := solver.state
	state.adapterOnce.Do(func() {
		state.adapterKey = key
		state.adapterValue = build(runtimeCheckResult(solver.contextID, state))
	})
	if state.adapterKey != key {
		panic("smt: immutable solver already has a different compatibility view")
	}
	return state.adapterValue
}

func runtimeCheckResult(context int, e *engine) CheckResult {
	e.publicOnce.Do(func() {
		e.publicContext = context
		status, booleans, integers, reals, bitVectors, reason := e.check()
		switch status {
		case checkSat:
			e.publicResult = Satisfiable{Value: modelValue{contextID: context, booleans: booleans, integers: integers, reals: reals, bitVectors: bitVectors, arrays: e.result.arrays, bitVectorArrays: e.result.bitVectorArrays}}
		case checkUnsat:
			e.publicResult = Unsatisfiable{Value: proofValue{contextID: context, assertions: len(e.assertions)}}
		default:
			e.publicResult = Unknown{Context: proofValue{contextID: context, assertions: len(e.assertions)}, Reason: reason}
		}
	})
	if e.publicContext != context {
		panic("smt: immutable engine reused with a different context witness")
	}
	return e.publicResult
}

type checkOutcome struct {
	status          int
	booleans        booleanModel
	integers        integerModel
	reals           rationalModel
	bitVectors      bitVectorModel
	arrays          *integerArrayModel
	bitVectorArrays *bitVectorArrayModel
	reason          UnknownReason
}

type integerModelEntry struct {
	id    int
	value IntegerValue
}

type integerModel struct {
	count    int
	inline   [4]integerModelEntry
	overflow map[int]IntegerValue
}

func (m *integerModel) reserve(count int) {
	if count > len(m.inline) {
		m.overflow = make(map[int]IntegerValue, count-len(m.inline))
	}
}

func (m *integerModel) set(id int, value IntegerValue) {
	if m.count < len(m.inline) {
		m.inline[m.count] = integerModelEntry{id: id, value: value}
		m.count++
		return
	}
	if m.overflow == nil {
		m.overflow = make(map[int]IntegerValue)
	}
	m.overflow[id] = value
}

func (m integerModel) lookup(id int) (IntegerValue, bool) {
	for index := 0; index < m.count; index++ {
		if m.inline[index].id == id {
			return m.inline[index].value, true
		}
	}
	value, ok := m.overflow[id]
	return value, ok
}

func (m *integerModel) merge(other integerModel) {
	for index := 0; index < other.count; index++ {
		entry := other.inline[index]
		m.set(entry.id, entry.value)
	}
	for id, value := range other.overflow {
		m.set(id, value)
	}
}

type booleanModelEntry struct {
	id    int
	value bool
}

type booleanModel struct {
	count    int
	inline   [4]booleanModelEntry
	overflow map[int]bool
	external map[int]bool
}

func (m *booleanModel) reserve(count int) {
	if count > len(m.inline) {
		m.overflow = make(map[int]bool, count-len(m.inline))
	}
}

func (m *booleanModel) set(id int, value bool) {
	if m.count < len(m.inline) {
		m.inline[m.count] = booleanModelEntry{id: id, value: value}
		m.count++
		return
	}
	if m.overflow == nil {
		m.overflow = make(map[int]bool)
	}
	m.overflow[id] = value
}

func (m booleanModel) lookup(id int) (bool, bool) {
	if m.external != nil {
		value, ok := m.external[id]
		return value, ok
	}
	for index := 0; index < m.count; index++ {
		if m.inline[index].id == id {
			return m.inline[index].value, true
		}
	}
	value, ok := m.overflow[id]
	return value, ok
}

func newEngine() *engine { return &engine{} }

func (e *engine) asserted(formula Term[BoolSort]) *engine {
	next := &engine{}
	count := len(e.assertions) + 1
	if count <= len(next.inlineAssertions) {
		next.assertions = next.inlineAssertions[:count]
	} else {
		next.assertions = make([]Term[BoolSort], count)
	}
	copy(next.assertions, e.assertions)
	next.assertions[count-1] = formula
	return next
}

func runtimeContextID(context, assertion int) int {
	return (context+assertion)*(context+assertion+1) + assertion + 1
}

func (e *engine) check() (int, booleanModel, integerModel, rationalModel, bitVectorModel, UnknownReason) {
	e.checkOnce.Do(func() { e.result = e.solve() })
	return e.result.status, e.result.booleans, e.result.integers, e.result.reals, e.result.bitVectors, e.result.reason
}

func (e *engine) solve() checkOutcome {
	return e.solveAdditional(nil)
}

func (e *engine) solveAdditional(assumptions []Term[BoolSort]) checkOutcome {
	allAssertions := e.assertions
	if len(assumptions) != 0 {
		allAssertions = make([]Term[BoolSort], 0, len(e.assertions)+len(assumptions))
		allAssertions = append(allAssertions, e.assertions...)
		allAssertions = append(allAssertions, assumptions...)
	}
	allConstants := len(allAssertions) > 0
	for _, assertion := range allAssertions {
		constant, ok := assertion.(Bool)
		if !ok {
			allConstants = false
			break
		}
		if !constant.Value {
			return checkOutcome{status: checkUnsat}
		}
	}
	if allConstants {
		return checkOutcome{status: checkSat}
	}
	if outcome, recognized := solveCompactBitVectorArrayExchange(allAssertions); recognized {
		return outcome
	}
	if outcome, recognized := solveCompactArrayIntegerExchange(allAssertions); recognized {
		return outcome
	}
	integerTheory := false
	eufTheory := false
	realTheory := false
	sharedRealEUF := false
	bitVectorTheory := false
	arrayTheory := false
	for _, assertion := range allAssertions {
		arrayTheory = arrayTheory || containsArrayTheory(assertion)
		bitVectorTheory = bitVectorTheory || containsBitVectorTheory(assertion)
		shared := containsSharedRealEUF(assertion)
		integerTheory = integerTheory || containsIntegerTheory(assertion)
		eufTheory = eufTheory || containsEUF(assertion) || shared
		realTheory = realTheory || containsRealTheory(assertion)
		sharedRealEUF = sharedRealEUF || shared
	}
	activeTheories := 0
	for _, active := range []bool{arrayTheory, bitVectorTheory, integerTheory, eufTheory, realTheory} {
		if active {
			activeTheories++
		}
	}
	if activeTheories > 1 {
		if arrayTheory && bitVectorTheory && containsSymbolicBitVectorArrayIndices(allAssertions) {
			if outcome, recognized := solveSharedArrayBitVector(allAssertions); recognized {
				return outcome
			}
		}
		if arrayTheory && integerTheory {
			if outcome, recognized := solveSharedArrayInteger(allAssertions); recognized {
				return outcome
			}
		}
		if sharedRealEUF {
			if outcome, recognized := solveSharedRealEUF(allAssertions); recognized {
				return outcome
			}
		}
		if outcome, recognized := solveConjunctiveTheoryProduct(allAssertions); recognized {
			return outcome
		}
	}
	if arrayTheory {
		if outcome, recognized := solveArrayAssertions(allAssertions); recognized {
			return outcome
		}
		return checkOutcome{status: checkUnknown, reason: UnsupportedTheory{Name: "array expression outside the ground read-over-write fragment"}}
	}
	if bitVectorTheory {
		if outcome, recognized := solveBitVectorAssertions(allAssertions); recognized {
			return outcome
		}
		return checkOutcome{status: checkUnknown, reason: UnsupportedTheory{Name: "bit-vector expression outside the bit-blasted fragment"}}
	}
	if realTheory {
		if outcome, recognized := solveLinearRealAssertions(allAssertions); recognized {
			return outcome
		}
	}
	if eufTheory {
		if outcome, recognized := solveEUFAssertions(allAssertions); recognized {
			return outcome
		}
	}
	if integerTheory {
		if containsGeneralLinearIntegerAssertions(allAssertions) {
			if outcome, recognized := solveLinearIntegerAssertions(allAssertions); recognized {
				return outcome
			}
		}
		if outcome, recognized := solveDifferenceAssertions(allAssertions); recognized {
			return outcome
		}
		if outcome, recognized := solveLinearIntegerAssertions(allAssertions); recognized {
			return outcome
		}
	}
	termCount := 0
	for _, assertion := range e.assertions {
		termCount += booleanTermSize(assertion)
	}
	for _, assumption := range assumptions {
		termCount += booleanTermSize(assumption)
	}
	var encoder booleanEncoder
	encoder.initialize(termCount)
	for _, assertion := range e.assertions {
		literal, ok := encoder.term(assertion)
		if !ok {
			return checkOutcome{status: checkUnknown, reason: unsupportedReason(integerTheory, eufTheory, realTheory, sharedRealEUF)}
		}
		encoder.addClause(literal)
	}
	for _, assumption := range assumptions {
		literal, ok := encoder.term(assumption)
		if !ok {
			return checkOutcome{status: checkUnknown, reason: unsupportedReason(integerTheory, eufTheory, realTheory, sharedRealEUF)}
		}
		encoder.addClause(literal)
	}
	assignment, sat := solveCNF(encoder.nextVariable, encoder.literals, encoder.clauses)
	if !sat {
		return checkOutcome{status: checkUnsat}
	}
	return checkOutcome{status: checkSat, booleans: encoder.model(assignment)}
}

func unsupportedReason(integerTheory, eufTheory, realTheory, sharedRealEUF bool) UnknownReason {
	if sharedRealEUF {
		return UnsupportedTheory{Name: "shared EUF/linear-real equality exchange"}
	}
	if realTheory {
		return UnsupportedTheory{Name: "linear real arithmetic outside the conjunctive fragment"}
	}
	if eufTheory {
		return UnsupportedTheory{Name: "uninterpreted functions outside the ground-conjunction fragment"}
	}
	if integerTheory {
		return UnsupportedTheory{Name: "integer arithmetic"}
	}
	return UnsupportedTheory{Name: "unsupported Boolean term"}
}

func (e *engine) checkAssuming(assumptions []Term[BoolSort]) (int, booleanModel, integerModel, rationalModel, bitVectorModel, []int, UnknownReason) {
	outcome := e.solveAdditional(assumptions)
	if outcome.status != checkUnsat {
		return outcome.status, outcome.booleans, outcome.integers, outcome.reals, outcome.bitVectors, nil, outcome.reason
	}
	coreTerms := append([]Term[BoolSort](nil), assumptions...)
	coreIndices := make([]int, len(assumptions))
	for index := range coreIndices {
		coreIndices[index] = index
	}
	for index := 0; index < len(coreTerms); {
		candidate := make([]Term[BoolSort], 0, len(coreTerms)-1)
		candidate = append(candidate, coreTerms[:index]...)
		candidate = append(candidate, coreTerms[index+1:]...)
		if e.solveAdditional(candidate).status == checkUnsat {
			coreTerms = candidate
			coreIndices = append(coreIndices[:index], coreIndices[index+1:]...)
			continue
		}
		index++
	}
	return checkUnsat, booleanModel{}, integerModel{}, rationalModel{}, bitVectorModel{}, coreIndices, nil
}

func evaluateBool(term Term[BoolSort], booleans booleanModel, integers integerModel, reals rationalModel) (bool, bool) {
	switch value := term.(type) {
	case Bool:
		return value.Value, true
	case BoolSymbol:
		return booleans.lookup(value.ID)
	case BooleanVariable:
		return booleans.lookup(value.ID)
	case NegatedBooleanVariable:
		result, ok := booleans.lookup(value.ID)
		return !result, ok
	case BooleanClause:
		return evaluateBooleanLiterals(value.Literals, booleans)
	case BooleanCNF:
		start := 0
		for _, end := range value.ClauseEnds {
			if end < start || end > len(value.Literals) {
				return false, false
			}
			result, ok := evaluateBooleanLiterals(value.Literals[start:end], booleans)
			if !ok || !result {
				return result, ok
			}
			start = end
		}
		return start == len(value.Literals), start == len(value.Literals)
	case Not:
		result, ok := evaluateBool(value.Value, booleans, integers, reals)
		return !result, ok
	case And:
		for _, item := range value.Values {
			result, ok := evaluateBool(item, booleans, integers, reals)
			if !ok {
				return false, false
			}
			if !result {
				return false, true
			}
		}
		return true, true
	case BooleanConjunction:
		terms, negated := value.values()
		for index, item := range terms {
			result, ok := evaluateBool(item, booleans, integers, reals)
			if !ok || result == negated[index] {
				return false, ok
			}
		}
		return true, true
	case TheoryConjunction:
		terms, negated := value.atomValues()
		for index, item := range terms {
			result, ok := evaluateBool(item, booleans, integers, reals)
			if !ok || result == negated[index] {
				return false, ok
			}
		}
		for _, constraint := range value.realValues() {
			result, ok := evaluateLinearRealConstraint(constraint, reals)
			if !ok || !result {
				return result, ok
			}
		}
		return true, true
	case Or:
		for _, item := range value.Values {
			result, ok := evaluateBool(item, booleans, integers, reals)
			if !ok {
				return false, false
			}
			if result {
				return true, true
			}
		}
		return false, true
	case Implies:
		left, leftOK := evaluateBool(value.Left, booleans, integers, reals)
		right, rightOK := evaluateBool(value.Right, booleans, integers, reals)
		return !left || right, leftOK && rightOK
	case Iff:
		left, leftOK := evaluateBool(value.Left, booleans, integers, reals)
		right, rightOK := evaluateBool(value.Right, booleans, integers, reals)
		return left == right, leftOK && rightOK
	case If[BoolSort]:
		condition, ok := evaluateBool(value.Condition, booleans, integers, reals)
		if !ok {
			return false, false
		}
		if condition {
			return evaluateBool(value.Then, booleans, integers, reals)
		}
		return evaluateBool(value.Else, booleans, integers, reals)
	case Equal:
		if left, ok := value.Left.(Term[BoolSort]); ok {
			right, rightOK := value.Right.(Term[BoolSort])
			if !rightOK {
				return false, false
			}
			leftValue, leftOK := evaluateBool(left, booleans, integers, reals)
			rightValue, rightValueOK := evaluateBool(right, booleans, integers, reals)
			return leftValue == rightValue, leftOK && rightValueOK
		}
		if left, ok := value.Left.(Term[IntSort]); ok {
			right, rightOK := value.Right.(Term[IntSort])
			if !rightOK {
				return false, false
			}
			leftValue, leftOK := evaluateInteger(left, booleans, integers, reals)
			rightValue, rightValueOK := evaluateInteger(right, booleans, integers, reals)
			return CompareIntegerValue(leftValue, rightValue) == 0, leftOK && rightValueOK
		}
		if left, ok := value.Left.(Term[RealSort]); ok {
			right, rightOK := value.Right.(Term[RealSort])
			if !rightOK {
				return false, false
			}
			leftValue, leftOK := evaluateReal(left, booleans, integers, reals)
			rightValue, rightValueOK := evaluateReal(right, booleans, integers, reals)
			return rationalCmp(leftValue, rightValue) == 0, leftOK && rightValueOK
		}
		return false, false
	case LessEqual:
		left, leftOK := evaluateInteger(value.Left, booleans, integers, reals)
		right, rightOK := evaluateInteger(value.Right, booleans, integers, reals)
		return CompareIntegerValue(left, right) <= 0, leftOK && rightOK
	case Less:
		left, leftOK := evaluateInteger(value.Left, booleans, integers, reals)
		right, rightOK := evaluateInteger(value.Right, booleans, integers, reals)
		return CompareIntegerValue(left, right) < 0, leftOK && rightOK
	case RealLessEqual:
		left, leftOK := evaluateReal(value.Left, booleans, integers, reals)
		right, rightOK := evaluateReal(value.Right, booleans, integers, reals)
		return rationalCmp(left, right) <= 0, leftOK && rightOK
	case RealLess:
		left, leftOK := evaluateReal(value.Left, booleans, integers, reals)
		right, rightOK := evaluateReal(value.Right, booleans, integers, reals)
		return rationalCmp(left, right) < 0, leftOK && rightOK
	case LinearRealConstraint:
		return evaluateLinearRealConstraint(value, reals)
	case LinearRealSystem:
		for _, constraint := range value.values() {
			result, ok := evaluateLinearRealConstraint(constraint, reals)
			if !ok || !result {
				return result, ok
			}
		}
		return true, true
	default:
		return false, false
	}
}

func evaluateLinearRealConstraint(value LinearRealConstraint, reals rationalModel) (bool, bool) {
	result := value.Constant
	symbols, coefficients := value.coefficientValues()
	for index, id := range symbols {
		item, ok := reals.lookup(id)
		if !ok {
			return false, false
		}
		result = rationalAdd(result, rationalMul(coefficients[index], item))
	}
	if value.Strict {
		return result.Sign() < 0, true
	}
	return result.Sign() <= 0, true
}

func evaluateReal(term Term[RealSort], booleans booleanModel, integers integerModel, reals rationalModel) (Rational, bool) {
	switch value := term.(type) {
	case Real:
		return value.Value, true
	case RealSymbol:
		return reals.lookup(value.ID)
	case RealAdd:
		result := Rational{}
		for _, item := range value.Values {
			next, ok := evaluateReal(item, booleans, integers, reals)
			if !ok {
				return Rational{}, false
			}
			result = rationalAdd(result, next)
		}
		return result, true
	case RealSubtract:
		left, leftOK := evaluateReal(value.Left, booleans, integers, reals)
		right, rightOK := evaluateReal(value.Right, booleans, integers, reals)
		return rationalSub(left, right), leftOK && rightOK
	case RealScale:
		item, ok := evaluateReal(value.Value, booleans, integers, reals)
		return rationalMul(value.Coefficient, item), ok
	case If[RealSort]:
		condition, ok := evaluateBool(value.Condition, booleans, integers, reals)
		if !ok {
			return Rational{}, false
		}
		if condition {
			return evaluateReal(value.Then, booleans, integers, reals)
		}
		return evaluateReal(value.Else, booleans, integers, reals)
	default:
		return Rational{}, false
	}
}

func evaluateBooleanLiterals(literals []int, booleans booleanModel) (bool, bool) {
	for _, literal := range literals {
		if literal == 0 {
			return false, false
		}
		id := literal - 1
		if literal < 0 {
			id = -literal - 1
		}
		value, ok := booleans.lookup(id)
		if !ok {
			return false, false
		}
		if value == (literal > 0) {
			return true, true
		}
	}
	return false, true
}

func evaluateInt(term Term[IntSort], booleans booleanModel, integers integerModel, reals rationalModel) (int64, bool) {
	value, ok := evaluateInteger(term, booleans, integers, reals)
	if !ok {
		return 0, false
	}
	return value.Int64()
}

func evaluateInteger(term Term[IntSort], booleans booleanModel, integers integerModel, reals rationalModel) (IntegerValue, bool) {
	return evaluateIntegerWithBitVectors(term, booleans, integers, reals, bitVectorModel{})
}

func evaluateIntegerWithBitVectors(term Term[IntSort], booleans booleanModel, integers integerModel, reals rationalModel, bitVectors bitVectorModel) (IntegerValue, bool) {
	switch value := term.(type) {
	case Integer:
		return NewIntegerValue(value.Value), true
	case integerExact[IntSort]:
		return value.value, true
	case IntSymbol:
		return integers.lookup(value.ID)
	case integerVariable[IntSort]:
		return integers.lookup(value.iD)
	case Add:
		total := IntegerValue{}
		for _, item := range value.Values {
			next, ok := evaluateIntegerWithBitVectors(item, booleans, integers, reals, bitVectors)
			if !ok {
				return IntegerValue{}, false
			}
			total = AddIntegerValue(total, next)
		}
		return total, true
	case Subtract:
		left, leftOK := evaluateIntegerWithBitVectors(value.Left, booleans, integers, reals, bitVectors)
		right, rightOK := evaluateIntegerWithBitVectors(value.Right, booleans, integers, reals, bitVectors)
		return SubIntegerValue(left, right), leftOK && rightOK
	case IntegerScale:
		operand, ok := evaluateIntegerWithBitVectors(value.Value, booleans, integers, reals, bitVectors)
		if !ok {
			return IntegerValue{}, false
		}
		return MultiplyIntegerValue(value.Coefficient, operand), true
	case If[IntSort]:
		condition, ok := evaluateBool(value.Condition, booleans, integers, reals)
		if !ok {
			return IntegerValue{}, false
		}
		if condition {
			return evaluateIntegerWithBitVectors(value.Then, booleans, integers, reals, bitVectors)
		}
		return evaluateIntegerWithBitVectors(value.Else, booleans, integers, reals, bitVectors)
	case bitVectorToInteger[IntSort]:
		operand, ok := evaluateBitVector(value.value, bitVectors, integers)
		if !ok {
			return IntegerValue{}, false
		}
		return BitVectorToIntegerValue(operand, value.signed), true
	default:
		return IntegerValue{}, false
	}
}
