package smt

// LinearRealConstraint is a compact affine relation used by compatibility
// layers that already normalized a linear expression. The inline form keeps
// common constraints allocation-free; the overflow fields preserve an
// unbounded surface for larger expressions.
type LinearRealConstraint struct {
	Count                int
	Symbols              [4]int
	Coefficients         [4]Rational
	OverflowSymbols      []int
	OverflowCoefficients []Rational
	Constant             Rational
	Strict               bool
}

// RealSymbolEquality is the normalized equality of two named real symbols.
type RealSymbolEquality struct {
	LeftID  int
	RightID int
}

func (RealSymbolEquality) isTerm(BoolSort) {}

// RealValueAssignment is the compact exact assignment of a named Real symbol.
type RealValueAssignment struct {
	ID    int
	Value Rational
}

func (RealValueAssignment) isTerm(BoolSort) {}

// RealUnaryComparison compares one Real->Real application with an exact
// constant. When ApplicationOnLeft is true it denotes f(x) op Bound;
// otherwise it denotes Bound op f(x). Strict selects < instead of <=.
type RealUnaryComparison struct {
	FunctionID        int
	ArgumentID        int
	Bound             Rational
	ApplicationOnLeft bool
	Strict            bool
}

func (RealUnaryComparison) isTerm(BoolSort) {}

// RealBinaryComparison compares one Real×Real->Real application with an exact
// rational bound without boxing the application tree.
type RealBinaryComparison struct {
	FunctionID        int
	FirstArgumentID   int
	SecondArgumentID  int
	Bound             Rational
	ApplicationOnLeft bool
	Strict            bool
}

func (RealBinaryComparison) isTerm(BoolSort) {}

// RealTernaryComparison compares one Real×Real×Real->Real application with
// an exact rational bound without boxing the application tree.
type RealTernaryComparison struct {
	FunctionID        int
	FirstArgumentID   int
	SecondArgumentID  int
	ThirdArgumentID   int
	Bound             Rational
	ApplicationOnLeft bool
	Strict            bool
}

func (RealTernaryComparison) isTerm(BoolSort) {}

func (LinearRealConstraint) isTerm(BoolSort) {}

// LinearRealSystem is an allocation-conscious conjunction of normalized
// affine constraints. Four relations cover common small solver queries;
// overflow remains available for unbounded inputs.
type LinearRealSystem struct {
	Count    int
	Inline   [4]LinearRealConstraint
	Overflow []LinearRealConstraint
}

func (LinearRealSystem) isTerm(BoolSort) {}

func (system LinearRealSystem) values() []LinearRealConstraint {
	if system.Overflow != nil {
		return system.Overflow[:system.Count]
	}
	return system.Inline[:system.Count]
}

func (constraint LinearRealConstraint) coefficientValues() ([]int, []Rational) {
	if constraint.OverflowSymbols != nil {
		return constraint.OverflowSymbols[:constraint.Count], constraint.OverflowCoefficients[:constraint.Count]
	}
	return constraint.Symbols[:constraint.Count], constraint.Coefficients[:constraint.Count]
}

type rationalLinearTerm struct {
	constant     Rational
	coefficients rationalCoefficients
	valid        bool
}

type rationalCoefficient struct {
	id    int
	value Rational
}

type rationalCoefficients struct {
	count    int
	inline   [4]rationalCoefficient
	overflow []rationalCoefficient
}

func (coefficients *rationalCoefficients) values() []rationalCoefficient {
	if coefficients.overflow != nil {
		return coefficients.overflow[:coefficients.count]
	}
	return coefficients.inline[:coefficients.count]
}

func (coefficients *rationalCoefficients) add(id int, value Rational) {
	for index := range coefficients.values() {
		if coefficients.values()[index].id == id {
			coefficients.values()[index].value = rationalAdd(coefficients.values()[index].value, value)
			return
		}
	}
	if coefficients.count < len(coefficients.inline) && coefficients.overflow == nil {
		coefficients.inline[coefficients.count] = rationalCoefficient{id: id, value: value}
		coefficients.count++
		return
	}
	if coefficients.overflow == nil {
		coefficients.overflow = make([]rationalCoefficient, coefficients.count, coefficients.count*2)
		copy(coefficients.overflow, coefficients.inline[:coefficients.count])
	}
	coefficients.overflow = append(coefficients.overflow, rationalCoefficient{id: id, value: value})
	coefficients.count++
}

func (coefficients *rationalCoefficients) compact() {
	kept := 0
	values := coefficients.values()
	for _, coefficient := range values {
		if coefficient.value.Sign() != 0 {
			values[kept] = coefficient
			kept++
		}
	}
	coefficients.count = kept
	if coefficients.overflow != nil {
		coefficients.overflow = coefficients.overflow[:kept]
	}
}

type rationalConstraint struct {
	coefficients rationalCoefficients
	bound        Rational
	strict       bool
}

type rationalProblem struct {
	constraintCount   int
	inlineConstraints [8]rationalConstraint
	constraints       []rationalConstraint
	symbolCount       int
	inlineSymbols     [8]int
	symbols           []int
	unsat             bool
}

func (problem *rationalProblem) constraintValues() []rationalConstraint {
	if problem.constraints != nil {
		return problem.constraints[:problem.constraintCount]
	}
	return problem.inlineConstraints[:problem.constraintCount]
}

func (problem *rationalProblem) appendConstraint(constraint rationalConstraint) {
	if problem.constraintCount < len(problem.inlineConstraints) && problem.constraints == nil {
		problem.inlineConstraints[problem.constraintCount] = constraint
		problem.constraintCount++
		return
	}
	if problem.constraints == nil {
		problem.constraints = make([]rationalConstraint, problem.constraintCount, problem.constraintCount*2)
		copy(problem.constraints, problem.inlineConstraints[:problem.constraintCount])
	}
	problem.constraints = append(problem.constraints, constraint)
	problem.constraintCount++
}

func (problem *rationalProblem) symbolValues() []int {
	if problem.symbols != nil {
		return problem.symbols[:problem.symbolCount]
	}
	return problem.inlineSymbols[:problem.symbolCount]
}

func (problem *rationalProblem) symbolPosition(id int) int {
	for position, symbol := range problem.symbolValues() {
		if symbol == id {
			return position
		}
	}
	return -1
}

func (problem *rationalProblem) appendSymbol(id int) {
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

func containsRealTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			if containsRealTheory(item) {
				return true
			}
		}
	case BooleanConjunction:
		terms, _ := value.values()
		for _, item := range terms {
			if containsRealTheory(item) {
				return true
			}
		}
	case TheoryConjunction:
		if value.RealCount != 0 || value.SymbolEqualityCount != 0 ||
			value.UnaryComparisonCount != 0 || value.BinaryComparisonCount != 0 ||
			value.TernaryComparisonCount != 0 {
			return true
		}
		terms, _ := value.atomValues()
		for _, item := range terms {
			if containsRealTheory(item) {
				return true
			}
		}
	case Or:
		for _, item := range value.Values {
			if containsRealTheory(item) {
				return true
			}
		}
	case Not:
		return containsRealTheory(value.Value)
	case Implies:
		return containsRealTheory(value.Left) || containsRealTheory(value.Right)
	case Iff:
		return containsRealTheory(value.Left) || containsRealTheory(value.Right)
	case If[BoolSort]:
		return containsRealTheory(value.Condition) || containsRealTheory(value.Then) || containsRealTheory(value.Else)
	case Equal:
		_, left := value.Left.(Term[RealSort])
		_, right := value.Right.(Term[RealSort])
		return left || right
	case RealLessEqual, RealLess:
		return true
	case LinearRealConstraint:
		return true
	case LinearRealSystem:
		return true
	case RealUnaryEquality:
		return true
	case RealSymbolEquality, RealValueAssignment, RealUnaryComparison, RealBinaryComparison, RealTernaryComparison:
		return true
	}
	return false
}

func solveLinearRealAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	return solveLinearRealParts(assertions, nil)
}

func solveLinearRealParts(assertions []Term[BoolSort], compact []LinearRealConstraint) (checkOutcome, bool) {
	problem := rationalProblem{}
	for _, assertion := range assertions {
		if !problem.boolean(assertion) {
			return checkOutcome{}, false
		}
	}
	for _, constraint := range compact {
		if !problem.compactConstraint(constraint) {
			return checkOutcome{}, false
		}
	}
	return problem.solve()
}

func (problem *rationalProblem) solve() (checkOutcome, bool) {
	if problem.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	strict := false
	for _, constraint := range problem.constraintValues() {
		strict = strict || constraint.strict
	}
	originals := problem.symbolCount
	transformed := originals * 2
	delta := -1
	if strict {
		delta = transformed
		transformed++
	}
	rows := problem.constraintCount
	if strict {
		rows++ // delta <= 1; non-negativity is inherent in simplex variables.
	}
	denseCount := rows * transformed
	arenaCount := denseCount + rows + transformed + transformed
	var inlineArena [64]Rational
	var arena []Rational
	if arenaCount <= len(inlineArena) {
		arena = inlineArena[:arenaCount]
	} else {
		arena = make([]Rational, arenaCount)
	}
	a := arena[:denseCount]
	b := arena[denseCount : denseCount+rows]
	objective := arena[denseCount+rows : denseCount+rows+transformed]
	values := arena[denseCount+rows+transformed:]
	for row, constraint := range problem.constraintValues() {
		for _, coefficient := range constraint.coefficients.values() {
			position := problem.symbolPosition(coefficient.id)
			a[row*transformed+position*2] = coefficient.value
			a[row*transformed+position*2+1] = rationalNeg(coefficient.value)
		}
		if constraint.strict {
			a[row*transformed+delta] = NewRational(1, 1)
		}
		b[row] = constraint.bound
	}
	if strict {
		a[(rows-1)*transformed+delta] = NewRational(1, 1)
		b[rows-1] = NewRational(1, 1)
		objective[delta] = NewRational(1, 1)
	}
	optimum, feasible := solveRationalSimplex(a, b, objective, values)
	if !feasible || strict && optimum.Sign() <= 0 {
		return checkOutcome{status: checkUnsat}, true
	}
	model := rationalModel{}
	if originals > len(model.inline) {
		model.overflow = make([]rationalModelEntry, 0, originals)
	}
	for position, id := range problem.symbolValues() {
		model.set(id, rationalSub(values[position*2], values[position*2+1]))
	}
	return checkOutcome{status: checkSat, reals: model}, true
}

func (problem *rationalProblem) boolean(term Term[BoolSort]) bool {
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
	case RealLessEqual:
		return problem.constraint(value.Left, value.Right, false)
	case RealLess:
		return problem.constraint(value.Left, value.Right, true)
	case Equal:
		left, leftOK := value.Left.(Term[RealSort])
		right, rightOK := value.Right.(Term[RealSort])
		if !leftOK || !rightOK {
			return false
		}
		return problem.constraint(left, right, false) && problem.constraint(right, left, false)
	case RealSymbolEquality:
		left := RealSymbol{ID: value.LeftID}
		right := RealSymbol{ID: value.RightID}
		return problem.constraint(left, right, false) && problem.constraint(right, left, false)
	case RealValueAssignment:
		symbol := RealSymbol{ID: value.ID}
		constant := Real{Value: value.Value}
		return problem.constraint(symbol, constant, false) &&
			problem.constraint(constant, symbol, false)
	case LinearRealConstraint:
		return problem.compactConstraint(value)
	case LinearRealSystem:
		for _, constraint := range value.values() {
			if !problem.compactConstraint(constraint) {
				return false
			}
		}
		return true
	default:
		return false
	}
}

func (problem *rationalProblem) compactConstraint(value LinearRealConstraint) bool {
	coefficients := rationalCoefficients{}
	symbols, values := value.coefficientValues()
	for index, id := range symbols {
		coefficients.add(id, values[index])
		if problem.symbolPosition(id) < 0 {
			problem.appendSymbol(id)
		}
	}
	coefficients.compact()
	if coefficients.count == 0 {
		comparison := value.Constant.Sign()
		problem.unsat = problem.unsat || comparison > 0 || value.Strict && comparison == 0
		return true
	}
	problem.appendConstraint(rationalConstraint{coefficients: coefficients, bound: rationalNeg(value.Constant), strict: value.Strict})
	return true
}

func (problem *rationalProblem) constraint(left, right Term[RealSort], strict bool) bool {
	form := rationalLinearTerm{valid: true}
	accumulateRational(left, NewRational(1, 1), &form)
	accumulateRational(right, NewRational(-1, 1), &form)
	if !form.valid {
		return false
	}
	form.coefficients.compact()
	for _, coefficient := range form.coefficients.values() {
		if problem.symbolPosition(coefficient.id) < 0 {
			problem.appendSymbol(coefficient.id)
		}
	}
	if form.coefficients.count == 0 {
		comparison := form.constant.Sign()
		problem.unsat = problem.unsat || comparison > 0 || strict && comparison == 0
		return true
	}
	problem.appendConstraint(rationalConstraint{
		coefficients: form.coefficients,
		bound:        rationalNeg(form.constant),
		strict:       strict,
	})
	return true
}

func accumulateRational(term Term[RealSort], multiplier Rational, form *rationalLinearTerm) {
	if !form.valid {
		return
	}
	switch value := term.(type) {
	case Real:
		form.constant = rationalAdd(form.constant, rationalMul(multiplier, value.Value))
	case RealSymbol:
		form.coefficients.add(value.ID, multiplier)
	case RealAdd:
		for _, item := range value.Values {
			accumulateRational(item, multiplier, form)
		}
	case RealSubtract:
		accumulateRational(value.Left, multiplier, form)
		accumulateRational(value.Right, rationalNeg(multiplier), form)
	case RealScale:
		accumulateRational(value.Value, rationalMul(multiplier, value.Coefficient), form)
	default:
		form.valid = false
	}
}

type rationalSimplex struct {
	m, n             int
	inlineBasis      [8]int
	overflowBasis    []int
	inlineNonbasis   [17]int
	overflowNonbasis []int
	inlineTableau    [256]Rational
	overflowTableau  []Rational
}

func (solver *rationalSimplex) at(row, column int) *Rational {
	index := row*(solver.n+2) + column
	if solver.overflowTableau != nil {
		return &solver.overflowTableau[index]
	}
	return &solver.inlineTableau[index]
}

func (solver *rationalSimplex) basisAt(index int) int {
	if solver.overflowBasis != nil {
		return solver.overflowBasis[index]
	}
	return solver.inlineBasis[index]
}

func (solver *rationalSimplex) setBasis(index, value int) {
	if solver.overflowBasis != nil {
		solver.overflowBasis[index] = value
	} else {
		solver.inlineBasis[index] = value
	}
}

func (solver *rationalSimplex) nonbasisAt(index int) int {
	if solver.overflowNonbasis != nil {
		return solver.overflowNonbasis[index]
	}
	return solver.inlineNonbasis[index]
}

func (solver *rationalSimplex) setNonbasis(index, value int) {
	if solver.overflowNonbasis != nil {
		solver.overflowNonbasis[index] = value
	} else {
		solver.inlineNonbasis[index] = value
	}
}

func solveRationalSimplex(a []Rational, b, objective, values []Rational) (Rational, bool) {
	m, n := len(b), len(objective)
	if len(values) < n {
		panic("smt: rational simplex output arena is too small")
	}
	values = values[:n]
	clear(values)
	solver := rationalSimplex{m: m, n: n}
	if m > len(solver.inlineBasis) {
		solver.overflowBasis = make([]int, m)
	}
	if n+1 > len(solver.inlineNonbasis) {
		solver.overflowNonbasis = make([]int, n+1)
	}
	tableauCount := (m + 2) * (n + 2)
	if tableauCount > len(solver.inlineTableau) {
		solver.overflowTableau = make([]Rational, tableauCount)
	}
	for row := 0; row < m; row++ {
		for column := 0; column < n; column++ {
			*solver.at(row, column) = a[row*n+column]
		}
		solver.setBasis(row, n+row)
		*solver.at(row, n) = NewRational(-1, 1)
		*solver.at(row, n+1) = b[row]
	}
	for column := 0; column < n; column++ {
		solver.setNonbasis(column, column)
		*solver.at(m, column) = rationalNeg(objective[column])
	}
	solver.setNonbasis(n, -1)
	*solver.at(m+1, n) = NewRational(1, 1)
	row := 0
	for candidate := 1; candidate < m; candidate++ {
		if rationalCmp(*solver.at(candidate, n+1), *solver.at(row, n+1)) < 0 {
			row = candidate
		}
	}
	if m != 0 && solver.at(row, n+1).Sign() < 0 {
		solver.pivot(row, n)
		if !solver.simplex(1) || solver.at(m+1, n+1).Sign() < 0 {
			return Rational{}, false
		}
		for row := 0; row < m; row++ {
			if solver.basisAt(row) != -1 {
				continue
			}
			column := solver.entering(row)
			if column >= 0 {
				solver.pivot(row, column)
			}
		}
	}
	if !solver.simplex(2) {
		return Rational{}, false
	}
	for row := 0; row < m; row++ {
		if solver.basisAt(row) < n {
			values[solver.basisAt(row)] = *solver.at(row, n+1)
		}
	}
	return *solver.at(m, n+1), true
}

func (solver *rationalSimplex) pivot(row, column int) {
	pivot := *solver.at(row, column)
	for otherRow := 0; otherRow < solver.m+2; otherRow++ {
		if otherRow == row {
			continue
		}
		for otherColumn := 0; otherColumn < solver.n+2; otherColumn++ {
			if otherColumn == column {
				continue
			}
			adjustment := rationalQuo(rationalMul(*solver.at(row, otherColumn), *solver.at(otherRow, column)), pivot)
			*solver.at(otherRow, otherColumn) = rationalSub(*solver.at(otherRow, otherColumn), adjustment)
		}
	}
	for otherColumn := 0; otherColumn < solver.n+2; otherColumn++ {
		if otherColumn != column {
			*solver.at(row, otherColumn) = rationalQuo(*solver.at(row, otherColumn), pivot)
		}
	}
	for otherRow := 0; otherRow < solver.m+2; otherRow++ {
		if otherRow != row {
			*solver.at(otherRow, column) = rationalQuo(rationalNeg(*solver.at(otherRow, column)), pivot)
		}
	}
	*solver.at(row, column) = rationalQuo(NewRational(1, 1), pivot)
	basis := solver.basisAt(row)
	solver.setBasis(row, solver.nonbasisAt(column))
	solver.setNonbasis(column, basis)
}

func (solver *rationalSimplex) simplex(phase int) bool {
	objectiveRow := solver.m
	if phase == 1 {
		objectiveRow = solver.m + 1
	}
	for {
		column := -1
		for candidate := 0; candidate <= solver.n; candidate++ {
			if phase == 2 && solver.nonbasisAt(candidate) == -1 {
				continue
			}
			if column < 0 || rationalCmp(*solver.at(objectiveRow, candidate), *solver.at(objectiveRow, column)) < 0 || rationalCmp(*solver.at(objectiveRow, candidate), *solver.at(objectiveRow, column)) == 0 && solver.nonbasisAt(candidate) < solver.nonbasisAt(column) {
				column = candidate
			}
		}
		if column < 0 || solver.at(objectiveRow, column).Sign() >= 0 {
			return true
		}
		row := -1
		for candidate := 0; candidate < solver.m; candidate++ {
			if solver.at(candidate, column).Sign() <= 0 {
				continue
			}
			if row < 0 {
				row = candidate
				continue
			}
			left := rationalQuo(*solver.at(candidate, solver.n+1), *solver.at(candidate, column))
			right := rationalQuo(*solver.at(row, solver.n+1), *solver.at(row, column))
			if comparison := rationalCmp(left, right); comparison < 0 || comparison == 0 && solver.basisAt(candidate) < solver.basisAt(row) {
				row = candidate
			}
		}
		if row < 0 {
			return false
		}
		solver.pivot(row, column)
	}
}

func (solver *rationalSimplex) entering(row int) int {
	column := -1
	for candidate := 0; candidate <= solver.n; candidate++ {
		if solver.at(row, candidate).Sign() == 0 {
			continue
		}
		if column < 0 || solver.nonbasisAt(candidate) < solver.nonbasisAt(column) {
			column = candidate
		}
	}
	return column
}
