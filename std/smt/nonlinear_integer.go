package smt

const (
	nonlinearIntegerSymbolLimit    = 8
	nonlinearIntegerRelationLimit  = 8
	nonlinearIntegerCandidateLimit = 64
	nonlinearIntegerSearchLimit    = 4096
	nonlinearIntegerDivisorLimit   = 4096
)

type nonlinearIntegerProductRelation struct {
	leftID, rightID int
	target          IntegerValue
	negated         bool
	complete        bool
}

// IntegerProductRelation is the compact form of x*y = k (or x*y != k).
// It lets frontends preserve nonlinear integer semantics without allocating
// the equivalent generic expression tree.
type IntegerProductRelation struct {
	LeftID, RightID int
	Target          IntegerValue
	Negated         bool
}

func (IntegerProductRelation) isTerm(BoolSort) {}

// IntegerProductSystem is an allocation-free conjunction for the common
// bounded product fragment. Count selects relations from Inline first and
// Overflow when the conjunction is larger than the inline capacity.
type IntegerProductSystem struct {
	Count    int
	Inline   [4]IntegerProductRelation
	Overflow []IntegerProductRelation
}

func (IntegerProductSystem) isTerm(BoolSort) {}

type nonlinearIntegerCandidates struct {
	count  int
	values [nonlinearIntegerCandidateLimit]IntegerValue
}

func (values *nonlinearIntegerCandidates) add(value IntegerValue) bool {
	for index := 0; index < values.count; index++ {
		if CompareIntegerValue(values.values[index], value) == 0 {
			return true
		}
	}
	if values.count == len(values.values) {
		return false
	}
	values.values[values.count] = value
	values.count++
	return true
}

type nonlinearIntegerProblem struct {
	symbolCount    int
	symbols        [nonlinearIntegerSymbolLimit]int
	candidates     [nonlinearIntegerSymbolLimit]nonlinearIntegerCandidates
	domainComplete [nonlinearIntegerSymbolLimit]bool
	relationCount  int
	relations      [nonlinearIntegerRelationLimit]nonlinearIntegerProductRelation
	impossible     bool
}

func solveNonlinearIntegerAssertions(
	assertions []Term[BoolSort],
) (checkOutcome, bool) {
	problem := nonlinearIntegerProblem{}
	for _, assertion := range assertions {
		if !problem.boolean(assertion, false) {
			return checkOutcome{}, false
		}
	}
	if problem.relationCount == 0 {
		return checkOutcome{}, false
	}
	if problem.impossible {
		return checkOutcome{status: checkUnsat}, true
	}
	problem.addEscapeCandidates()
	var assigned [nonlinearIntegerSymbolLimit]bool
	var values [nonlinearIntegerSymbolLimit]IntegerValue
	nodes := 0
	if problem.search(0, &assigned, &values, &nodes) {
		var model integerModel
		model.reserve(problem.symbolCount)
		for index := 0; index < problem.symbolCount; index++ {
			model.set(problem.symbols[index], values[index])
		}
		return checkOutcome{status: checkSat, integers: model}, true
	}
	if nodes > nonlinearIntegerSearchLimit {
		return checkOutcome{
			status: checkUnknown,
			reason: ResourceLimit{Limit: nonlinearIntegerSearchLimit},
		}, true
	}
	if problem.allDomainsComplete() {
		return checkOutcome{status: checkUnsat}, true
	}
	return checkOutcome{
		status: checkUnknown,
		reason: UnsupportedTheory{
			Name: "nonlinear integer factor search outside the bounded exact fragment",
		},
	}, true
}

func (problem *nonlinearIntegerProblem) boolean(
	term Term[BoolSort], negated bool,
) bool {
	switch value := term.(type) {
	case And:
		if negated {
			return false
		}
		for _, item := range value.Values {
			if !problem.boolean(item, false) {
				return false
			}
		}
		return true
	case BooleanConjunction:
		if negated {
			return false
		}
		items, polarities := value.values()
		for index, item := range items {
			if !problem.boolean(item, polarities[index]) {
				return false
			}
		}
		return true
	case Not:
		return problem.boolean(value.Value, !negated)
	case Equal:
		return problem.equality(value.Left, value.Right, negated)
	case IntegerProductRelation:
		value.Negated = value.Negated != negated
		return problem.addRelation(value)
	case IntegerProductSystem:
		if negated || value.Count < 0 {
			return false
		}
		relations := value.Overflow
		if value.Count <= len(value.Inline) {
			relations = value.Inline[:value.Count]
		} else if len(relations) != value.Count {
			return false
		}
		for _, relation := range relations {
			if !problem.addRelation(relation) {
				return false
			}
		}
		return true
	default:
		return false
	}
}

func (problem *nonlinearIntegerProblem) equality(
	left, right any, negated bool,
) bool {
	product, target, ok := nonlinearIntegerProductEquality(left, right)
	if !ok {
		product, target, ok = nonlinearIntegerProductEquality(right, left)
	}
	if !ok {
		return false
	}
	leftID, leftOK := directIntegerSymbolID(product.Left)
	rightID, rightOK := directIntegerSymbolID(product.Right)
	if !leftOK || !rightOK {
		return false
	}
	return problem.addRelation(IntegerProductRelation{
		LeftID: leftID, RightID: rightID, Target: target, Negated: negated,
	})
}

func (problem *nonlinearIntegerProblem) addRelation(
	value IntegerProductRelation,
) bool {
	if problem.relationCount == len(problem.relations) {
		return false
	}
	leftID, rightID := value.LeftID, value.RightID
	for _, existing := range problem.relations[:problem.relationCount] {
		samePair := existing.leftID == leftID && existing.rightID == rightID ||
			existing.leftID == rightID && existing.rightID == leftID
		if !samePair {
			continue
		}
		sameTarget := CompareIntegerValue(existing.target, value.Target) == 0
		if (!existing.negated && !value.Negated && !sameTarget) ||
			(sameTarget && existing.negated != value.Negated) {
			problem.impossible = true
			return true
		}
	}
	leftPosition, leftAdded := problem.ensureSymbol(leftID)
	rightPosition, rightAdded := problem.ensureSymbol(rightID)
	if !leftAdded || !rightAdded {
		return false
	}
	relation := nonlinearIntegerProductRelation{
		leftID: leftID, rightID: rightID, target: value.Target,
		negated: value.Negated, complete: true,
	}
	if leftID == rightID && !value.Negated {
		if CompareIntegerValue(value.Target, IntegerValue{}) < 0 {
			problem.impossible = true
		} else {
			rootValue := value.Target.big()
			rootValue.Sqrt(rootValue)
			root := integerValueFromBig(rootValue)
			if CompareIntegerValue(
				MultiplyIntegerValue(root, root), value.Target,
			) != 0 {
				problem.impossible = true
			} else {
				problem.candidates[leftPosition].add(root)
				problem.candidates[leftPosition].add(
					NegateIntegerValue(root),
				)
				problem.domainComplete[leftPosition] = true
			}
		}
	} else {
		relation.complete = problem.addFactorCandidates(
			leftPosition, rightPosition, value.Target,
		)
		if !value.Negated &&
			CompareIntegerValue(value.Target, IntegerValue{}) != 0 &&
			relation.complete {
			problem.domainComplete[leftPosition] = true
			problem.domainComplete[rightPosition] = true
		}
	}
	problem.candidates[leftPosition].add(IntegerValue{})
	problem.candidates[leftPosition].add(NewIntegerValue(1))
	problem.candidates[leftPosition].add(NewIntegerValue(-1))
	problem.candidates[rightPosition].add(IntegerValue{})
	problem.candidates[rightPosition].add(NewIntegerValue(1))
	problem.candidates[rightPosition].add(NewIntegerValue(-1))
	problem.relations[problem.relationCount] = relation
	problem.relationCount++
	return true
}

func (problem *nonlinearIntegerProblem) addEscapeCandidates() {
	escape := NewIntegerValue(1)
	for _, relation := range problem.relations[:problem.relationCount] {
		absolute := relation.target
		if CompareIntegerValue(absolute, IntegerValue{}) < 0 {
			absolute = NegateIntegerValue(absolute)
		}
		candidate := AddIntegerValue(absolute, NewIntegerValue(1))
		if CompareIntegerValue(candidate, escape) > 0 {
			escape = candidate
		}
	}
	for position := 0; position < problem.symbolCount; position++ {
		if problem.domainComplete[position] {
			continue
		}
		problem.candidates[position].add(escape)
		problem.candidates[position].add(NegateIntegerValue(escape))
	}
}

func (problem *nonlinearIntegerProblem) allDomainsComplete() bool {
	for position := 0; position < problem.symbolCount; position++ {
		if !problem.domainComplete[position] {
			return false
		}
	}
	return true
}

func nonlinearIntegerProductEquality(
	productTerm, targetTerm any,
) (IntegerMultiply, IntegerValue, bool) {
	product, ok := productTerm.(IntegerMultiply)
	if !ok {
		return IntegerMultiply{}, IntegerValue{}, false
	}
	targetExpression, ok := targetTerm.(Term[IntSort])
	if !ok {
		return IntegerMultiply{}, IntegerValue{}, false
	}
	target, ok := evaluateInteger(
		targetExpression,
		booleanModel{}, integerModel{}, rationalModel{},
	)
	return product, target, ok
}

func (problem *nonlinearIntegerProblem) ensureSymbol(id int) (int, bool) {
	for index := 0; index < problem.symbolCount; index++ {
		if problem.symbols[index] == id {
			return index, true
		}
	}
	if problem.symbolCount == len(problem.symbols) {
		return 0, false
	}
	position := problem.symbolCount
	problem.symbols[position] = id
	problem.symbolCount++
	return position, true
}

func (problem *nonlinearIntegerProblem) addFactorCandidates(
	left, right int, target IntegerValue,
) bool {
	problem.candidates[left].add(target)
	problem.candidates[left].add(NegateIntegerValue(target))
	problem.candidates[right].add(target)
	problem.candidates[right].add(NegateIntegerValue(target))
	inline, ok := target.Int64()
	if !ok || inline == -1<<63 {
		return false
	}
	if inline < 0 {
		inline = -inline
	}
	if inline == 0 {
		return true
	}
	complete := true
	divisor := int64(1)
	for ; divisor <= inline/divisor; divisor++ {
		if divisor > nonlinearIntegerDivisorLimit {
			complete = false
			break
		}
		if inline%divisor != 0 {
			continue
		}
		quotient := inline / divisor
		for _, factor := range [4]int64{
			divisor, -divisor, quotient, -quotient,
		} {
			if !problem.candidates[left].add(NewIntegerValue(factor)) ||
				!problem.candidates[right].add(NewIntegerValue(factor)) {
				return false
			}
		}
	}
	return complete
}

func (problem *nonlinearIntegerProblem) symbolPosition(id int) int {
	for index := 0; index < problem.symbolCount; index++ {
		if problem.symbols[index] == id {
			return index
		}
	}
	return -1
}

func (problem *nonlinearIntegerProblem) search(
	position int,
	assigned *[nonlinearIntegerSymbolLimit]bool,
	values *[nonlinearIntegerSymbolLimit]IntegerValue,
	nodes *int,
) bool {
	*nodes++
	if *nodes > nonlinearIntegerSearchLimit {
		return false
	}
	if position == problem.symbolCount {
		return problem.valid(assigned, values)
	}
	candidates := problem.candidates[position]
	for _, candidate := range candidates.values[:candidates.count] {
		assigned[position], values[position] = true, candidate
		if problem.valid(assigned, values) &&
			problem.search(position+1, assigned, values, nodes) {
			return true
		}
	}
	assigned[position] = false
	return false
}

func (problem *nonlinearIntegerProblem) valid(
	assigned *[nonlinearIntegerSymbolLimit]bool,
	values *[nonlinearIntegerSymbolLimit]IntegerValue,
) bool {
	for _, relation := range problem.relations[:problem.relationCount] {
		left := problem.symbolPosition(relation.leftID)
		right := problem.symbolPosition(relation.rightID)
		if left < 0 || right < 0 || !assigned[left] || !assigned[right] {
			continue
		}
		holds := CompareIntegerValue(
			MultiplyIntegerValue(values[left], values[right]),
			relation.target,
		) == 0
		if holds == relation.negated {
			return false
		}
	}
	return true
}
