package smt

import "math/big"

const linearIntegerBranchLimit = 4096

// IntegerLinearEquality is the allocation-conscious normal form a
// compatibility layer can use for coefficient*x = value.
type IntegerLinearEquality struct {
	ID          int
	Coefficient int64
	Value       IntegerValue
}

func (IntegerLinearEquality) isTerm(BoolSort) {}

func CompactIntegerLinearEquality(left, right Term[IntSort]) (IntegerLinearEquality, bool) {
	form := linearInteger{valid: true}
	accumulateInteger(left, 1, &form)
	accumulateInteger(right, -1, &form)
	if !form.valid || len(form.overflow) != 0 {
		return IntegerLinearEquality{}, false
	}
	result := IntegerLinearEquality{Value: NegateIntegerValue(form.constant)}
	count := 0
	for index := 0; index < form.count; index++ {
		term := form.inline[index]
		if term.coefficient != 0 {
			result.ID, result.Coefficient, count = term.id, term.coefficient, count+1
		}
	}
	return result, count == 1
}

func containsGeneralLinearInteger(term any) bool {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			if containsGeneralLinearInteger(item) {
				return true
			}
		}
	case BooleanConjunction:
		terms, _ := value.values()
		for _, item := range terms {
			if containsGeneralLinearInteger(item) {
				return true
			}
		}
	case Equal:
		return containsGeneralLinearInteger(value.Left) || containsGeneralLinearInteger(value.Right)
	case LessEqual:
		return containsGeneralLinearInteger(value.Left) || containsGeneralLinearInteger(value.Right)
	case Less:
		return containsGeneralLinearInteger(value.Left) || containsGeneralLinearInteger(value.Right)
	case Add:
		for _, item := range value.Values {
			if containsGeneralLinearInteger(item) {
				return true
			}
		}
	case Subtract:
		return containsGeneralLinearInteger(value.Left) || containsGeneralLinearInteger(value.Right)
	case IntegerScale, IntegerLinearEquality:
		return true
	}
	return false
}

func containsGeneralLinearIntegerAssertions(assertions []Term[BoolSort]) bool {
	for _, assertion := range assertions {
		if containsGeneralLinearInteger(assertion) {
			return true
		}
	}
	return false
}

type integerLinearConstraint struct {
	coefficients integerCoefficients
	bound        IntegerValue
}

type integerLinearProblem struct {
	constraintCount   int
	inlineConstraints [8]integerLinearConstraint
	constraints       []integerLinearConstraint
	symbolCount       int
	inlineSymbols     [8]int
	symbols           []int
	unsat             bool
}

type integerAffine struct {
	constant     IntegerValue
	coefficients integerCoefficients
	valid        bool
}

type integerCoefficient struct {
	id    int
	value IntegerValue
}

type integerCoefficients struct {
	count    int
	inline   [4]integerCoefficient
	overflow []integerCoefficient
}

func (coefficients *integerCoefficients) values() []integerCoefficient {
	if coefficients.overflow != nil {
		return coefficients.overflow[:coefficients.count]
	}
	return coefficients.inline[:coefficients.count]
}

func (coefficients *integerCoefficients) add(id int, value IntegerValue) {
	values := coefficients.values()
	for index := range values {
		if values[index].id == id {
			values[index].value = AddIntegerValue(values[index].value, value)
			return
		}
	}
	if coefficients.count < len(coefficients.inline) && coefficients.overflow == nil {
		coefficients.inline[coefficients.count] = integerCoefficient{id: id, value: value}
		coefficients.count++
		return
	}
	if coefficients.overflow == nil {
		coefficients.overflow = make([]integerCoefficient, coefficients.count, coefficients.count*2)
		copy(coefficients.overflow, coefficients.inline[:coefficients.count])
	}
	coefficients.overflow = append(coefficients.overflow, integerCoefficient{id: id, value: value})
	coefficients.count++
}

func (coefficients *integerCoefficients) compact() {
	values := coefficients.values()
	kept := 0
	for _, coefficient := range values {
		if CompareIntegerValue(coefficient.value, IntegerValue{}) != 0 {
			values[kept] = coefficient
			kept++
		}
	}
	coefficients.count = kept
	if coefficients.overflow != nil {
		coefficients.overflow = coefficients.overflow[:kept]
	}
}

func (problem *integerLinearProblem) constraintValues() []integerLinearConstraint {
	if problem.constraints != nil {
		return problem.constraints[:problem.constraintCount]
	}
	return problem.inlineConstraints[:problem.constraintCount]
}

func (problem *integerLinearProblem) appendConstraint(constraint integerLinearConstraint) {
	if problem.constraintCount < len(problem.inlineConstraints) && problem.constraints == nil {
		problem.inlineConstraints[problem.constraintCount] = constraint
		problem.constraintCount++
		return
	}
	if problem.constraints == nil {
		problem.constraints = make([]integerLinearConstraint, problem.constraintCount, problem.constraintCount*2)
		copy(problem.constraints, problem.inlineConstraints[:problem.constraintCount])
	}
	problem.constraints = append(problem.constraints, constraint)
	problem.constraintCount++
}

func (problem *integerLinearProblem) symbolValues() []int {
	if problem.symbols != nil {
		return problem.symbols[:problem.symbolCount]
	}
	return problem.inlineSymbols[:problem.symbolCount]
}

func (problem *integerLinearProblem) addSymbol(id int) {
	for _, existing := range problem.symbolValues() {
		if existing == id {
			return
		}
	}
	if problem.symbolCount < len(problem.inlineSymbols) && problem.symbols == nil {
		problem.inlineSymbols[problem.symbolCount] = id
		problem.symbolCount++
		return
	}
	if problem.symbols == nil {
		problem.symbols = make([]int, problem.symbolCount, problem.symbolCount*2)
		copy(problem.symbols, problem.inlineSymbols[:problem.symbolCount])
	}
	problem.symbols = append(problem.symbols, id)
	problem.symbolCount++
}

// solveLinearIntegerAssertions decides conjunctive QF_LIA with exact
// arbitrary-precision coefficients. It uses the existing exact rational
// simplex as a relaxation and branches only on fractional integer values.
func solveLinearIntegerAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if outcome, recognized := solveSingleVariableLinearIntegerEquality(assertions); recognized {
		return outcome, true
	}
	problem := integerLinearProblem{}
	for _, assertion := range assertions {
		if !problem.boolean(assertion) {
			return checkOutcome{}, false
		}
	}
	if problem.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	nodes := 0
	outcome, exhausted := problem.branch(nil, &nodes)
	if exhausted {
		return checkOutcome{status: checkUnknown, reason: ResourceLimit{Limit: linearIntegerBranchLimit}}, true
	}
	return outcome, true
}

func solveSingleVariableLinearIntegerEquality(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if len(assertions) != 1 {
		return checkOutcome{}, false
	}
	equality, ok := assertions[0].(Equal)
	if compact, compactOK := assertions[0].(IntegerLinearEquality); compactOK {
		return solveCompactIntegerLinearEquality(compact), true
	}
	if !ok {
		return checkOutcome{}, false
	}
	left, leftOK := equality.Left.(Term[IntSort])
	right, rightOK := equality.Right.(Term[IntSort])
	if !leftOK || !rightOK {
		return checkOutcome{}, false
	}
	form := linearInteger{valid: true}
	accumulateInteger(left, 1, &form)
	accumulateInteger(right, -1, &form)
	if !form.valid || len(form.overflow) != 0 {
		return checkOutcome{}, false
	}
	id, coefficient, count := 0, int64(0), 0
	for index := 0; index < form.count; index++ {
		term := form.inline[index]
		if term.coefficient != 0 {
			id, coefficient, count = term.id, term.coefficient, count+1
		}
	}
	if count == 0 {
		if CompareIntegerValue(form.constant, IntegerValue{}) == 0 {
			return checkOutcome{status: checkSat}, true
		}
		return checkOutcome{status: checkUnsat}, true
	}
	if count != 1 {
		return checkOutcome{}, false
	}
	if form.constant.large == nil && form.constant.small != -1<<63 {
		numerator := -form.constant.small
		if numerator%coefficient != 0 {
			return checkOutcome{status: checkUnsat}, true
		}
		model := integerModel{}
		model.set(id, NewIntegerValue(numerator/coefficient))
		return checkOutcome{status: checkSat, integers: model}, true
	}
	numerator := NegateIntegerValue(form.constant).big()
	denominator := big.NewInt(coefficient)
	quotient, remainder := new(big.Int), new(big.Int)
	quotient.QuoRem(numerator, denominator, remainder)
	if remainder.Sign() != 0 {
		return checkOutcome{status: checkUnsat}, true
	}
	model := integerModel{}
	model.set(id, integerValueFromBig(quotient))
	return checkOutcome{status: checkSat, integers: model}, true
}

func solveCompactIntegerLinearEquality(value IntegerLinearEquality) checkOutcome {
	if value.Coefficient == 0 {
		if CompareIntegerValue(value.Value, IntegerValue{}) == 0 {
			return checkOutcome{status: checkSat}
		}
		return checkOutcome{status: checkUnsat}
	}
	if value.Value.large == nil && value.Value.small != -1<<63 {
		if value.Value.small%value.Coefficient != 0 {
			return checkOutcome{status: checkUnsat}
		}
		model := integerModel{}
		model.set(value.ID, NewIntegerValue(value.Value.small/value.Coefficient))
		return checkOutcome{status: checkSat, integers: model}
	}
	quotient, remainder := new(big.Int), new(big.Int)
	quotient.QuoRem(value.Value.big(), big.NewInt(value.Coefficient), remainder)
	if remainder.Sign() != 0 {
		return checkOutcome{status: checkUnsat}
	}
	model := integerModel{}
	model.set(value.ID, integerValueFromBig(quotient))
	return checkOutcome{status: checkSat, integers: model}
}

func (problem *integerLinearProblem) boolean(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case Bool:
		problem.unsat = problem.unsat || !value.Value
		return true
	case And:
		for _, item := range value.Values {
			if !problem.boolean(item) {
				return false
			}
		}
		return true
	case BooleanConjunction:
		terms, negated := value.values()
		for index, item := range terms {
			if negated[index] || !problem.boolean(item) {
				return false
			}
		}
		return true
	case LessEqual:
		return problem.relation(value.Left, value.Right, false)
	case Less:
		return problem.relation(value.Left, value.Right, true)
	case Equal:
		left, leftOK := value.Left.(Term[IntSort])
		right, rightOK := value.Right.(Term[IntSort])
		return leftOK && rightOK && problem.relation(left, right, false) && problem.relation(right, left, false)
	case IntegerDifferenceConstraint:
		return problem.compactDifference(value)
	case IntegerDifferenceSystem:
		for _, constraint := range value.values() {
			if !problem.compactDifference(constraint) {
				return false
			}
		}
		return true
	case IntegerLinearEquality:
		coefficient := NewIntegerValue(value.Coefficient)
		first, second := integerCoefficients{}, integerCoefficients{}
		first.add(value.ID, coefficient)
		second.add(value.ID, NegateIntegerValue(coefficient))
		problem.appendConstraint(integerLinearConstraint{coefficients: first, bound: value.Value})
		problem.appendConstraint(integerLinearConstraint{coefficients: second, bound: NegateIntegerValue(value.Value)})
		problem.addSymbol(value.ID)
		return true
	default:
		return false
	}
}

func (problem *integerLinearProblem) compactDifference(value IntegerDifferenceConstraint) bool {
	bound := NewIntegerValue(value.Bound)
	if value.Wide {
		bound = value.WideBound
	}
	if value.Strict {
		bound = AddIntegerValue(bound, NewIntegerValue(-1))
	}
	coefficients := integerCoefficients{}
	if value.HasPositive {
		coefficients.add(value.PositiveID, NewIntegerValue(1))
	}
	if value.HasNegative {
		coefficients.add(value.NegativeID, NewIntegerValue(-1))
	}
	if coefficients.count == 0 {
		problem.unsat = problem.unsat || CompareIntegerValue(IntegerValue{}, bound) > 0
		return true
	}
	for _, coefficient := range coefficients.values() {
		problem.addSymbol(coefficient.id)
	}
	problem.appendConstraint(integerLinearConstraint{coefficients: coefficients, bound: bound})
	return true
}

func (problem *integerLinearProblem) relation(left, right Term[IntSort], strict bool) bool {
	form := integerAffine{valid: true}
	accumulateIntegerAffine(left, NewIntegerValue(1), &form)
	accumulateIntegerAffine(right, NewIntegerValue(-1), &form)
	if !form.valid {
		return false
	}
	bound := NegateIntegerValue(form.constant)
	if strict {
		bound = AddIntegerValue(bound, NewIntegerValue(-1))
	}
	form.coefficients.compact()
	for _, coefficient := range form.coefficients.values() {
		problem.addSymbol(coefficient.id)
	}
	if form.coefficients.count == 0 {
		problem.unsat = problem.unsat || CompareIntegerValue(IntegerValue{}, bound) > 0
		return true
	}
	problem.appendConstraint(integerLinearConstraint{coefficients: form.coefficients, bound: bound})
	return true
}

func accumulateIntegerAffine(term Term[IntSort], multiplier IntegerValue, form *integerAffine) {
	if !form.valid {
		return
	}
	switch value := term.(type) {
	case Integer:
		form.constant = AddIntegerValue(form.constant, MultiplyIntegerValue(multiplier, NewIntegerValue(value.Value)))
	case integerExact[IntSort]:
		form.constant = AddIntegerValue(form.constant, MultiplyIntegerValue(multiplier, value.value))
	case IntSymbol:
		form.add(value.ID, multiplier)
	case integerVariable[IntSort]:
		form.add(value.iD, multiplier)
	case Add:
		for _, item := range value.Values {
			accumulateIntegerAffine(item, multiplier, form)
		}
	case Subtract:
		accumulateIntegerAffine(value.Left, multiplier, form)
		accumulateIntegerAffine(value.Right, NegateIntegerValue(multiplier), form)
	case IntegerScale:
		accumulateIntegerAffine(value.Value, MultiplyIntegerValue(multiplier, value.Coefficient), form)
	default:
		form.valid = false
	}
}

func (form *integerAffine) add(id int, coefficient IntegerValue) {
	form.coefficients.add(id, coefficient)
}

func (problem *integerLinearProblem) branch(extra []integerLinearConstraint, nodes *int) (checkOutcome, bool) {
	*nodes++
	if *nodes > linearIntegerBranchLimit {
		return checkOutcome{}, true
	}
	relaxation := rationalProblem{}
	for _, id := range problem.symbolValues() {
		relaxation.appendSymbol(id)
	}
	appendConstraint := func(constraint integerLinearConstraint) {
		coefficients := rationalCoefficients{}
		for _, coefficient := range constraint.coefficients.values() {
			coefficients.add(coefficient.id, rationalFromInteger(coefficient.value))
		}
		coefficients.compact()
		relaxation.appendConstraint(rationalConstraint{coefficients: coefficients, bound: rationalFromInteger(constraint.bound)})
	}
	for _, constraint := range problem.constraintValues() {
		appendConstraint(constraint)
	}
	for _, constraint := range extra {
		appendConstraint(constraint)
	}
	result, _ := relaxation.solve()
	if result.status == checkUnsat {
		return result, false
	}
	for _, id := range problem.symbolValues() {
		value, _ := result.reals.lookup(id)
		if value.IsInteger() {
			continue
		}
		floor := floorRational(value)
		ceil := AddIntegerValue(floor, NewIntegerValue(1))
		leftCoefficients := integerCoefficients{}
		leftCoefficients.add(id, NewIntegerValue(1))
		left := integerLinearConstraint{coefficients: leftCoefficients, bound: floor}
		if outcome, exhausted := problem.branch(append(extra, left), nodes); exhausted || outcome.status == checkSat {
			return outcome, exhausted
		}
		rightCoefficients := integerCoefficients{}
		rightCoefficients.add(id, NewIntegerValue(-1))
		right := integerLinearConstraint{coefficients: rightCoefficients, bound: NegateIntegerValue(ceil)}
		return problem.branch(append(extra, right), nodes)
	}
	model := integerModel{}
	model.reserve(problem.symbolCount)
	for _, id := range problem.symbolValues() {
		value, _ := result.reals.lookup(id)
		integer, ok := integerFromRational(value)
		if !ok {
			return checkOutcome{status: checkUnknown, reason: UnsupportedTheory{Name: "non-integral QF_LIA model"}}, false
		}
		model.set(id, integer)
	}
	return checkOutcome{status: checkSat, integers: model}, false
}

func integerFromRational(value Rational) (IntegerValue, bool) {
	if numerator, denominator, ok := value.small(); ok {
		if denominator != 1 {
			return IntegerValue{}, false
		}
		return NewIntegerValue(numerator), true
	}
	if !value.large.IsInt() {
		return IntegerValue{}, false
	}
	return integerValueFromBig(value.large.Num()), true
}

func rationalFromInteger(value IntegerValue) Rational {
	if value.large == nil {
		return NewRational(value.small, 1)
	}
	return rationalFromBig(new(big.Rat).SetInt(value.big()))
}

func floorRational(value Rational) IntegerValue {
	if numerator, denominator, ok := value.small(); ok {
		quotient := numerator / denominator
		if numerator < 0 && numerator%denominator != 0 {
			quotient--
		}
		return NewIntegerValue(quotient)
	}
	fraction := value.big()
	return integerValueFromBig(new(big.Int).Div(fraction.Num(), fraction.Denom()))
}
