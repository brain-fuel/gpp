package smt

import "math"

type differenceEdge struct {
	from   int
	to     int
	weight IntegerValue
}

type differenceProblem struct {
	edges           []differenceEdge
	inlineEdges     [8]differenceEdge
	inlineSymbols   [8]differenceSymbolNode
	symbolCount     int
	overflowSymbols map[int]int
	unsat           bool
	unknown         bool
}

type linearInteger struct {
	constant IntegerValue
	inline   [4]linearIntegerTerm
	count    int
	overflow map[int]int64
	valid    bool
}

type linearIntegerTerm struct {
	id          int
	coefficient int64
}

type differenceSymbolNode struct {
	id   int
	node int
}

type IntegerDifferenceConstraint struct {
	PositiveID  int
	NegativeID  int
	HasPositive bool
	HasNegative bool
	Bound       int64
	WideBound   IntegerValue
	Wide        bool
	Strict      bool
}

func (IntegerDifferenceConstraint) isTerm(BoolSort) {}

type IntegerDifferenceSystem struct {
	Count    int
	Inline   [4]IntegerDifferenceConstraint
	Overflow []IntegerDifferenceConstraint
}

func (IntegerDifferenceSystem) isTerm(BoolSort) {}

func (value IntegerDifferenceSystem) values() []IntegerDifferenceConstraint {
	if value.Overflow != nil {
		return value.Overflow[:value.Count]
	}
	return value.Inline[:value.Count]
}

func containsIntegerTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			if containsIntegerTheory(item) {
				return true
			}
		}
	case BooleanConjunction:
		terms, _ := value.values()
		for _, item := range terms {
			if containsIntegerTheory(item) {
				return true
			}
		}
	case TheoryConjunction:
		terms, _ := value.atomValues()
		for _, item := range terms {
			if containsIntegerTheory(item) {
				return true
			}
		}
	case Or:
		for _, item := range value.Values {
			if containsIntegerTheory(item) {
				return true
			}
		}
	case Not:
		return containsIntegerTheory(value.Value)
	case Implies:
		return containsIntegerTheory(value.Left) || containsIntegerTheory(value.Right)
	case Iff:
		return containsIntegerTheory(value.Left) || containsIntegerTheory(value.Right)
	case If[BoolSort]:
		return containsIntegerTheory(value.Condition) || containsIntegerTheory(value.Then) || containsIntegerTheory(value.Else)
	case Equal:
		_, leftIsInteger := value.Left.(Term[IntSort])
		_, rightIsInteger := value.Right.(Term[IntSort])
		return leftIsInteger || rightIsInteger
	case LessEqual, Less:
		return true
	case IntegerDifferenceConstraint, IntegerDifferenceSystem:
		return true
	case IntegerLinearEquality, IntegerLinearDisequality, IntegerLinearChoice, integerLinearStrictBound, IntegerDivModRelation, IntegerDivModSystem:
		return true
	case IntegerProductRelation, IntegerProductSystem:
		return true
	case IntegerUnaryComparison, IntegerBinaryComparison, IntegerTernaryComparison:
		return true
	}
	return false
}

// solveDifferenceAssertions recognizes conjunctions of integer difference
// constraints. Its Boolean result says whether the entire assertion set was
// in QF_IDL; unrecognized formulas continue through the SAT/theory path.
func solveDifferenceAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	problem := differenceProblem{}
	problem.edges = problem.inlineEdges[:0]
	for _, assertion := range assertions {
		if !problem.boolean(assertion) {
			return checkOutcome{}, false
		}
	}
	if problem.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	var inlineDistance [9]IntegerValue
	distanceCount := problem.symbolsLen() + 1
	var distance []IntegerValue
	if distanceCount <= len(inlineDistance) {
		distance = inlineDistance[:distanceCount]
	} else {
		distance = make([]IntegerValue, distanceCount)
	}
	for iteration := 0; iteration < len(distance); iteration++ {
		changed := false
		for _, edge := range problem.edges {
			candidate := AddIntegerValue(distance[edge.from], edge.weight)
			if CompareIntegerValue(candidate, distance[edge.to]) < 0 {
				distance[edge.to] = candidate
				changed = true
				if iteration == len(distance)-1 {
					return checkOutcome{status: checkUnsat}, true
				}
			}
		}
		if !changed {
			break
		}
	}
	var model integerModel
	model.reserve(problem.symbolsLen())
	offset := NegateIntegerValue(distance[0])
	for index := 0; index < problem.symbolCount; index++ {
		symbol := problem.inlineSymbols[index]
		value := AddIntegerValue(distance[symbol.node], offset)
		model.set(symbol.id, value)
	}
	for id, node := range problem.overflowSymbols {
		value := AddIntegerValue(distance[node], offset)
		model.set(id, value)
	}
	return checkOutcome{status: checkSat, integers: model}, true
}

func differenceEntailsEquality(assertions []Term[BoolSort], leftID, rightID int) (bool, bool) {
	problem := differenceProblem{}
	problem.edges = problem.inlineEdges[:0]
	for _, assertion := range assertions {
		if !problem.boolean(assertion) {
			return false, false
		}
	}
	if problem.unsat {
		return true, true
	}
	left, right := problem.node(leftID), problem.node(rightID)
	return problem.pathAtMost(left, right, IntegerValue{}) && problem.pathAtMost(right, left, IntegerValue{}), true
}

func (problem *differenceProblem) pathAtMost(from, to int, bound IntegerValue) bool {
	count := problem.symbolsLen() + 1
	var inlineDistance [9]IntegerValue
	var inlineReached [9]bool
	var distance []IntegerValue
	var reached []bool
	if count <= len(inlineDistance) {
		distance, reached = inlineDistance[:count], inlineReached[:count]
	} else {
		distance, reached = make([]IntegerValue, count), make([]bool, count)
	}
	reached[from] = true
	for iteration := 0; iteration < count-1; iteration++ {
		changed := false
		for _, edge := range problem.edges {
			if !reached[edge.from] {
				continue
			}
			candidate := AddIntegerValue(distance[edge.from], edge.weight)
			if !reached[edge.to] || CompareIntegerValue(candidate, distance[edge.to]) < 0 {
				distance[edge.to], reached[edge.to], changed = candidate, true, true
			}
		}
		if !changed {
			break
		}
	}
	return reached[to] && CompareIntegerValue(distance[to], bound) <= 0
}

func (p *differenceProblem) node(id int) int {
	for index := 0; index < p.symbolCount; index++ {
		if p.inlineSymbols[index].id == id {
			return p.inlineSymbols[index].node
		}
	}
	if node, ok := p.overflowSymbols[id]; ok {
		return node
	}
	node := p.symbolsLen() + 1
	if p.symbolCount < len(p.inlineSymbols) {
		p.inlineSymbols[p.symbolCount] = differenceSymbolNode{id: id, node: node}
		p.symbolCount++
		return node
	}
	if p.overflowSymbols == nil {
		p.overflowSymbols = make(map[int]int)
	}
	p.overflowSymbols[id] = node
	return node
}

func (p *differenceProblem) symbolsLen() int {
	return p.symbolCount + len(p.overflowSymbols)
}

func (p *differenceProblem) boolean(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case Bool:
		p.unsat = p.unsat || !value.Value
		return true
	case And:
		for _, item := range value.Values {
			if !p.boolean(item) {
				return false
			}
		}
		return true
	case BooleanConjunction:
		terms, negated := value.values()
		for index, item := range terms {
			if negated[index] || !p.boolean(item) {
				return false
			}
		}
		return true
	case LessEqual:
		return p.constraint(value.Left, value.Right, false)
	case Less:
		return p.constraint(value.Left, value.Right, true)
	case Equal:
		left, leftOK := value.Left.(Term[IntSort])
		right, rightOK := value.Right.(Term[IntSort])
		if !leftOK || !rightOK {
			return false
		}
		return p.constraint(left, right, false) && p.constraint(right, left, false)
	case IntegerDifferenceConstraint:
		return p.compactConstraint(value)
	case IntegerDifferenceSystem:
		for _, constraint := range value.values() {
			if !p.compactConstraint(constraint) {
				return false
			}
		}
		return true
	case IntegerLinearEquality, IntegerLinearDisequality, IntegerLinearChoice, integerLinearStrictBound, IntegerDivModRelation, IntegerDivModSystem:
		return false
	default:
		return false
	}
}

func (p *differenceProblem) compactConstraint(value IntegerDifferenceConstraint) bool {
	bound := NewIntegerValue(value.Bound)
	if value.Wide {
		bound = value.WideBound
	}
	if value.Strict {
		bound = AddIntegerValue(bound, NewIntegerValue(-1))
	}
	positive, negative := 0, 0
	if value.HasPositive {
		positive = p.node(value.PositiveID)
	}
	if value.HasNegative {
		negative = p.node(value.NegativeID)
	}
	if !value.HasPositive && !value.HasNegative {
		p.unsat = p.unsat || CompareIntegerValue(IntegerValue{}, bound) > 0
		return true
	}
	p.edges = append(p.edges, differenceEdge{from: negative, to: positive, weight: bound})
	return true
}

func (p *differenceProblem) constraint(left, right Term[IntSort], strict bool) bool {
	form := linearInteger{valid: true}
	accumulateInteger(left, 1, &form)
	accumulateInteger(right, -1, &form)
	if !form.valid {
		return false
	}
	bound := NegateIntegerValue(form.constant)
	if strict {
		bound = AddIntegerValue(bound, NewIntegerValue(-1))
	}
	positive, negative := 0, 0
	hasPositive, hasNegative := false, false
	visit := func(id int, coefficient int64) bool {
		switch coefficient {
		case 0:
			return true
		case 1:
			if hasPositive {
				return false
			}
			positive = p.node(id)
			hasPositive = true
		case -1:
			if hasNegative {
				return false
			}
			negative = p.node(id)
			hasNegative = true
		default:
			return false
		}
		return true
	}
	for index := 0; index < form.count; index++ {
		term := form.inline[index]
		if !visit(term.id, term.coefficient) {
			return false
		}
	}
	for id, coefficient := range form.overflow {
		if !visit(id, coefficient) {
			return false
		}
	}
	if !hasPositive && !hasNegative {
		comparison := CompareIntegerValue(form.constant, IntegerValue{})
		p.unsat = p.unsat || comparison > 0 || (strict && comparison == 0)
		return true
	}
	p.edges = append(p.edges, differenceEdge{from: negative, to: positive, weight: bound})
	return true
}

func accumulateInteger(term Term[IntSort], multiplier int64, form *linearInteger) {
	if !form.valid {
		return
	}
	switch value := term.(type) {
	case Integer:
		product := NewIntegerValue(value.Value)
		if multiplier == -1 {
			product = NegateIntegerValue(product)
		}
		form.constant = AddIntegerValue(form.constant, product)
	case integerExact[IntSort]:
		product := value.value
		if multiplier == -1 {
			product = NegateIntegerValue(product)
		}
		form.constant = AddIntegerValue(form.constant, product)
	case IntSymbol:
		form.add(value.ID, multiplier)
	case integerVariable[IntSort]:
		form.add(value.iD, multiplier)
	case Add:
		for _, item := range value.Values {
			accumulateInteger(item, multiplier, form)
		}
	case Subtract:
		accumulateInteger(value.Left, multiplier, form)
		negated, ok := negateInt64(multiplier)
		if !ok {
			form.valid = false
			return
		}
		accumulateInteger(value.Right, negated, form)
	case IntegerScale:
		coefficient, ok := value.Coefficient.Int64()
		if !ok {
			form.valid = false
			return
		}
		scaled, ok := checkedMulInt64(multiplier, coefficient)
		if !ok {
			form.valid = false
			return
		}
		accumulateInteger(value.Value, scaled, form)
	default:
		form.valid = false
	}
}

func (form *linearInteger) add(id int, coefficient int64) {
	for index := 0; index < form.count; index++ {
		if form.inline[index].id == id {
			form.inline[index].coefficient, form.valid = addInt64(form.inline[index].coefficient, coefficient)
			return
		}
	}
	if existing, ok := form.overflow[id]; ok {
		form.overflow[id], form.valid = addInt64(existing, coefficient)
		return
	}
	if form.count < len(form.inline) {
		form.inline[form.count] = linearIntegerTerm{id: id, coefficient: coefficient}
		form.count++
		return
	}
	if form.overflow == nil {
		form.overflow = make(map[int]int64)
	}
	form.overflow[id] = coefficient
}

func addInt64(left, right int64) (int64, bool) {
	if right > 0 && left > math.MaxInt64-right || right < 0 && left < math.MinInt64-right {
		return 0, false
	}
	return left + right, true
}

func negateInt64(value int64) (int64, bool) {
	if value == math.MinInt64 {
		return 0, false
	}
	return -value, true
}

func multiplyInt64(value, multiplier int64) (int64, bool) {
	if multiplier == 1 {
		return value, true
	}
	if multiplier == -1 {
		return negateInt64(value)
	}
	return 0, false
}
