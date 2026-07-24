package smt

import "math"

const (
	nonlinearIntegerSymbolLimit    = 8
	nonlinearIntegerRelationLimit  = 8
	nonlinearIntegerCandidateLimit = 64
	nonlinearIntegerSearchLimit    = 4096
	nonlinearIntegerDivisorLimit   = 4096
)

type nonlinearIntegerProductRelation struct {
	left, right IntegerAffineFactor
	target      IntegerValue
	negated     bool
	complete    bool
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

// IntegerAffineFactor is coefficient*x + offset with one integer symbol.
type IntegerAffineFactor struct {
	SymbolID    int
	Coefficient IntegerValue
	Offset      IntegerValue
}

// IntegerAffineProductRelation is the compact form
// (a*x+b)*(c*y+d) = k (or != k).
type IntegerAffineProductRelation struct {
	Left, Right IntegerAffineFactor
	Target      IntegerValue
	Negated     bool
}

func (IntegerAffineProductRelation) isTerm(BoolSort) {}

type IntegerAffineProductSystem struct {
	Count    int
	Inline   [4]IntegerAffineProductRelation
	Overflow []IntegerAffineProductRelation
}

func (IntegerAffineProductSystem) isTerm(BoolSort) {}

// IntegerSquareBound represents x² <(=) k when Lower is false and
// k <(=) x² when Lower is true.
type IntegerSquareBound struct {
	SymbolID int
	Bound    IntegerValue
	Lower    bool
	Strict   bool
}

func (IntegerSquareBound) isTerm(BoolSort) {}

// IntegerSquareSystem is an allocation-free conjunction of self-square
// bounds for the bounded nonlinear integer fragment.
type IntegerSquareSystem struct {
	Count    int
	Inline   [4]IntegerSquareBound
	Overflow []IntegerSquareBound
}

func (IntegerSquareSystem) isTerm(BoolSort) {}

// IntegerAffineSquareBound represents (a*x+b)² <(=) k when Lower is false
// and k <(=) (a*x+b)² when Lower is true.
type IntegerAffineSquareBound struct {
	Factor IntegerAffineFactor
	Bound  IntegerValue
	Lower  bool
	Strict bool
}

func (IntegerAffineSquareBound) isTerm(BoolSort) {}

type IntegerAffineSquareSystem struct {
	Count    int
	Inline   [4]IntegerAffineSquareBound
	Overflow []IntegerAffineSquareBound
}

func (IntegerAffineSquareSystem) isTerm(BoolSort) {}

// IntegerProductBound represents x*y <(=) k when Lower is false and
// k <(=) x*y when Lower is true.
type IntegerProductBound struct {
	LeftID, RightID int
	Bound           IntegerValue
	Lower           bool
	Strict          bool
}

func (IntegerProductBound) isTerm(BoolSort) {}

// IntegerProductBoundSystem is an allocation-free conjunction of bilinear
// product bounds for the bounded nonlinear integer fragment.
type IntegerProductBoundSystem struct {
	Count    int
	Inline   [4]IntegerProductBound
	Overflow []IntegerProductBound
}

func (IntegerProductBoundSystem) isTerm(BoolSort) {}

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
	symbolCount       int
	symbols           [nonlinearIntegerSymbolLimit]int
	candidates        [nonlinearIntegerSymbolLimit]nonlinearIntegerCandidates
	domainComplete    [nonlinearIntegerSymbolLimit]bool
	relationCount     int
	relations         [nonlinearIntegerRelationLimit]nonlinearIntegerProductRelation
	boundCount        int
	bounds            [nonlinearIntegerRelationLimit]IntegerAffineSquareBound
	productBoundCount int
	productBounds     [nonlinearIntegerRelationLimit]IntegerProductBound
	impossible        bool
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
	if problem.relationCount == 0 && problem.boundCount == 0 &&
		problem.productBoundCount == 0 {
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
	case Less:
		return problem.squareComparison(
			value.Left, value.Right, true, negated,
		)
	case LessEqual:
		return problem.squareComparison(
			value.Left, value.Right, false, negated,
		)
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
	case IntegerAffineProductRelation:
		value.Negated = value.Negated != negated
		return problem.addAffineRelation(value)
	case IntegerAffineProductSystem:
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
			if !problem.addAffineRelation(relation) {
				return false
			}
		}
		return true
	case IntegerSquareBound:
		if negated {
			value.Lower = !value.Lower
			value.Strict = !value.Strict
		}
		return problem.addSquareBound(value)
	case IntegerSquareSystem:
		if negated || value.Count < 0 {
			return false
		}
		bounds := value.Overflow
		if value.Count <= len(value.Inline) {
			bounds = value.Inline[:value.Count]
		} else if len(bounds) != value.Count {
			return false
		}
		for _, bound := range bounds {
			if !problem.addSquareBound(bound) {
				return false
			}
		}
		return true
	case IntegerAffineSquareBound:
		if negated {
			value.Lower = !value.Lower
			value.Strict = !value.Strict
		}
		return problem.addAffineSquareBound(value)
	case IntegerAffineSquareSystem:
		if negated || value.Count < 0 {
			return false
		}
		bounds := value.Overflow
		if value.Count <= len(value.Inline) {
			bounds = value.Inline[:value.Count]
		} else if len(bounds) != value.Count {
			return false
		}
		for _, bound := range bounds {
			if !problem.addAffineSquareBound(bound) {
				return false
			}
		}
		return true
	case IntegerProductBound:
		if negated {
			value.Lower = !value.Lower
			value.Strict = !value.Strict
		}
		return problem.addProductBound(value)
	case IntegerProductBoundSystem:
		if negated || value.Count < 0 {
			return false
		}
		bounds := value.Overflow
		if value.Count <= len(value.Inline) {
			bounds = value.Inline[:value.Count]
		} else if len(bounds) != value.Count {
			return false
		}
		for _, bound := range bounds {
			if !problem.addProductBound(bound) {
				return false
			}
		}
		return true
	default:
		return false
	}
}

func (problem *nonlinearIntegerProblem) squareComparison(
	left, right Term[IntSort], strict, negated bool,
) bool {
	product, target, ok := nonlinearIntegerProductEquality(left, right)
	lower := false
	if !ok {
		product, target, ok = nonlinearIntegerProductEquality(right, left)
		lower = true
	}
	if !ok {
		return false
	}
	leftFactor, leftAffine := nonlinearIntegerAffineFactor(product.Left)
	rightFactor, rightAffine := nonlinearIntegerAffineFactor(product.Right)
	if leftAffine && rightAffine &&
		equalIntegerAffineFactor(leftFactor, rightFactor) {
		if negated {
			lower = !lower
			strict = !strict
		}
		return problem.addAffineSquareBound(IntegerAffineSquareBound{
			Factor: leftFactor, Bound: target, Lower: lower, Strict: strict,
		})
	}
	leftID, leftOK := directIntegerSymbolID(product.Left)
	rightID, rightOK := directIntegerSymbolID(product.Right)
	if !leftOK || !rightOK {
		return false
	}
	if negated {
		lower = !lower
		strict = !strict
	}
	return problem.addProductBound(IntegerProductBound{
		LeftID: leftID, RightID: rightID,
		Bound: target, Lower: lower, Strict: strict,
	})
}

func (problem *nonlinearIntegerProblem) addProductBound(
	bound IntegerProductBound,
) bool {
	if problem.productBoundCount == len(problem.productBounds) {
		return false
	}
	left, leftAdded := problem.ensureSymbol(bound.LeftID)
	right, rightAdded := problem.ensureSymbol(bound.RightID)
	if !leftAdded || !rightAdded {
		return false
	}
	witness := bound.Bound
	if bound.Strict {
		offset := int64(-1)
		if bound.Lower {
			offset = 1
		}
		witness = AddIntegerValue(witness, NewIntegerValue(offset))
	}
	problem.candidates[left].add(NewIntegerValue(1))
	problem.candidates[right].add(witness)
	problem.candidates[left].add(NewIntegerValue(-1))
	problem.candidates[right].add(NegateIntegerValue(witness))
	problem.candidates[left].add(IntegerValue{})
	problem.candidates[right].add(IntegerValue{})
	problem.productBounds[problem.productBoundCount] = bound
	problem.productBoundCount++
	return true
}

func (problem *nonlinearIntegerProblem) addSquareBound(
	bound IntegerSquareBound,
) bool {
	return problem.addAffineSquareBound(IntegerAffineSquareBound{
		Factor: IntegerAffineFactor{
			SymbolID: bound.SymbolID, Coefficient: NewIntegerValue(1),
		},
		Bound: bound.Bound, Lower: bound.Lower, Strict: bound.Strict,
	})
}

func (problem *nonlinearIntegerProblem) addAffineSquareBound(
	bound IntegerAffineSquareBound,
) bool {
	if problem.boundCount == len(problem.bounds) {
		return false
	}
	position, added := problem.ensureSymbol(bound.Factor.SymbolID)
	if !added {
		return false
	}
	zero := IntegerValue{}
	if bound.Lower {
		minimum := zero
		if CompareIntegerValue(bound.Bound, zero) >= 0 {
			root := integerSquareRoot(bound.Bound)
			exact := CompareIntegerValue(
				MultiplyIntegerValue(root, root), bound.Bound,
			) == 0
			minimum = root
			if bound.Strict || !exact {
				minimum = AddIntegerValue(minimum, NewIntegerValue(1))
			}
		}
		problem.addAffineFactorCandidate(position, bound.Factor, minimum)
		problem.addAffineFactorCandidate(
			position, bound.Factor, NegateIntegerValue(minimum),
		)
		large := AddIntegerValue(
			AddIntegerValue(
				absoluteIntegerValue(bound.Bound),
				absoluteIntegerValue(bound.Factor.Offset),
			),
			NewIntegerValue(2),
		)
		problem.candidates[position].add(large)
		problem.candidates[position].add(NegateIntegerValue(large))
	} else {
		if CompareIntegerValue(bound.Bound, zero) < 0 ||
			bound.Strict && CompareIntegerValue(bound.Bound, zero) == 0 {
			problem.impossible = true
		} else {
			maximum := integerSquareRoot(bound.Bound)
			if bound.Strict && CompareIntegerValue(
				MultiplyIntegerValue(maximum, maximum), bound.Bound,
			) == 0 {
				maximum = AddIntegerValue(maximum, NewIntegerValue(-1))
			}
			complete := problem.addAffineSquareRange(
				position, bound.Factor, maximum,
			)
			problem.domainComplete[position] =
				problem.domainComplete[position] || complete
		}
	}
	problem.bounds[problem.boundCount] = bound
	problem.boundCount++
	return true
}

func absoluteIntegerValue(value IntegerValue) IntegerValue {
	if CompareIntegerValue(value, IntegerValue{}) < 0 {
		return NegateIntegerValue(value)
	}
	return value
}

func integerSquareRoot(value IntegerValue) IntegerValue {
	if inline, ok := value.Int64(); ok && inline >= 0 {
		root := int64(math.Sqrt(float64(inline)))
		for root < inline && root+1 <= inline/(root+1) {
			root++
		}
		for root > 0 && root > inline/root {
			root--
		}
		return NewIntegerValue(root)
	}
	root := value.big()
	root.Sqrt(root)
	return integerValueFromBig(root)
}

func (problem *nonlinearIntegerProblem) addAffineSquareRange(
	position int, factor IntegerAffineFactor, maximum IntegerValue,
) bool {
	inline, ok := maximum.Int64()
	if !ok || inline < 0 ||
		inline > (nonlinearIntegerCandidateLimit-1)/2 {
		problem.addAffineFactorCandidate(
			position, factor, IntegerValue{},
		)
		problem.addAffineFactorCandidate(position, factor, maximum)
		problem.addAffineFactorCandidate(
			position, factor, NegateIntegerValue(maximum),
		)
		return false
	}
	for candidate := -inline; candidate <= inline; candidate++ {
		if !problem.addAffineFactorCandidate(
			position, factor, NewIntegerValue(candidate),
		) {
			return false
		}
	}
	return true
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
	leftFactor, leftOK := nonlinearIntegerAffineFactor(product.Left)
	rightFactor, rightOK := nonlinearIntegerAffineFactor(product.Right)
	if !leftOK || !rightOK {
		return false
	}
	return problem.addAffineRelation(IntegerAffineProductRelation{
		Left: leftFactor, Right: rightFactor, Target: target, Negated: negated,
	})
}

func (problem *nonlinearIntegerProblem) addRelation(
	value IntegerProductRelation,
) bool {
	one := NewIntegerValue(1)
	return problem.addAffineRelation(IntegerAffineProductRelation{
		Left: IntegerAffineFactor{
			SymbolID: value.LeftID, Coefficient: one,
		},
		Right: IntegerAffineFactor{
			SymbolID: value.RightID, Coefficient: one,
		},
		Target: value.Target, Negated: value.Negated,
	})
}

func (problem *nonlinearIntegerProblem) addAffineRelation(
	value IntegerAffineProductRelation,
) bool {
	if problem.relationCount == len(problem.relations) {
		return false
	}
	leftFactor, rightFactor := value.Left, value.Right
	for _, existing := range problem.relations[:problem.relationCount] {
		samePair := equalIntegerAffineFactor(existing.left, leftFactor) &&
			equalIntegerAffineFactor(existing.right, rightFactor) ||
			equalIntegerAffineFactor(existing.left, rightFactor) &&
				equalIntegerAffineFactor(existing.right, leftFactor)
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
	leftPosition, leftAdded := problem.ensureSymbol(leftFactor.SymbolID)
	rightPosition, rightAdded := problem.ensureSymbol(rightFactor.SymbolID)
	if !leftAdded || !rightAdded {
		return false
	}
	relation := nonlinearIntegerProductRelation{
		left: leftFactor, right: rightFactor, target: value.Target,
		negated: value.Negated, complete: true,
	}
	if equalIntegerAffineFactor(leftFactor, rightFactor) && !value.Negated {
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
				problem.addAffineFactorCandidate(
					leftPosition, leftFactor, root,
				)
				problem.addAffineFactorCandidate(
					leftPosition, leftFactor, NegateIntegerValue(root),
				)
				problem.domainComplete[leftPosition] = true
			}
		}
	} else {
		relation.complete = problem.addFactorCandidates(
			leftPosition, rightPosition, leftFactor, rightFactor, value.Target,
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

func equalIntegerAffineFactor(left, right IntegerAffineFactor) bool {
	return left.SymbolID == right.SymbolID &&
		CompareIntegerValue(left.Coefficient, right.Coefficient) == 0 &&
		CompareIntegerValue(left.Offset, right.Offset) == 0
}

func nonlinearIntegerAffineFactor(
	term Term[IntSort],
) (IntegerAffineFactor, bool) {
	form := integerAffine{valid: true}
	accumulateIntegerAffine(term, NewIntegerValue(1), &form)
	form.coefficients.compact()
	if !form.valid || form.coefficients.count != 1 {
		return IntegerAffineFactor{}, false
	}
	coefficient := form.coefficients.values()[0]
	return IntegerAffineFactor{
		SymbolID: coefficient.id, Coefficient: coefficient.value,
		Offset: form.constant,
	}, true
}

// CompactIntegerAffineFactor normalizes a one-symbol affine integer term for
// allocation-conscious solver frontends.
func CompactIntegerAffineFactor(
	term Term[IntSort],
) (IntegerAffineFactor, bool) {
	return nonlinearIntegerAffineFactor(term)
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
	left, right int,
	leftFactor, rightFactor IntegerAffineFactor,
	target IntegerValue,
) bool {
	problem.addAffineFactorCandidate(left, leftFactor, target)
	problem.addAffineFactorCandidate(
		left, leftFactor, NegateIntegerValue(target),
	)
	problem.addAffineFactorCandidate(right, rightFactor, target)
	problem.addAffineFactorCandidate(
		right, rightFactor, NegateIntegerValue(target),
	)
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
			value := NewIntegerValue(factor)
			if !problem.addAffineFactorCandidate(left, leftFactor, value) ||
				!problem.addAffineFactorCandidate(
					right, rightFactor, value,
				) {
				return false
			}
		}
	}
	return complete
}

func (problem *nonlinearIntegerProblem) addAffineFactorCandidate(
	position int, factor IntegerAffineFactor, value IntegerValue,
) bool {
	numerator := AddIntegerValue(value, NegateIntegerValue(factor.Offset))
	quotient, remainder, ok := DivModIntegerValue(
		numerator, factor.Coefficient,
	)
	if !ok {
		return false
	}
	if CompareIntegerValue(remainder, IntegerValue{}) != 0 {
		return true
	}
	return problem.candidates[position].add(quotient)
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
		left := problem.symbolPosition(relation.left.SymbolID)
		right := problem.symbolPosition(relation.right.SymbolID)
		if left < 0 || right < 0 || !assigned[left] || !assigned[right] {
			continue
		}
		holds := CompareIntegerValue(
			MultiplyIntegerValue(
				evaluateIntegerAffineFactor(relation.left, values[left]),
				evaluateIntegerAffineFactor(relation.right, values[right]),
			),
			relation.target,
		) == 0
		if holds == relation.negated {
			return false
		}
	}
	for _, bound := range problem.bounds[:problem.boundCount] {
		position := problem.symbolPosition(bound.Factor.SymbolID)
		if position < 0 || !assigned[position] {
			continue
		}
		comparison := CompareIntegerValue(
			MultiplyIntegerValue(
				evaluateIntegerAffineFactor(bound.Factor, values[position]),
				evaluateIntegerAffineFactor(bound.Factor, values[position]),
			),
			bound.Bound,
		)
		holds := comparison <= 0
		if bound.Strict {
			holds = comparison < 0
		}
		if bound.Lower {
			holds = comparison >= 0
			if bound.Strict {
				holds = comparison > 0
			}
		}
		if !holds {
			return false
		}
	}
	for _, bound := range problem.productBounds[:problem.productBoundCount] {
		left := problem.symbolPosition(bound.LeftID)
		right := problem.symbolPosition(bound.RightID)
		if left < 0 || right < 0 || !assigned[left] || !assigned[right] {
			continue
		}
		comparison := CompareIntegerValue(
			MultiplyIntegerValue(values[left], values[right]), bound.Bound,
		)
		holds := comparison <= 0
		if bound.Strict {
			holds = comparison < 0
		}
		if bound.Lower {
			holds = comparison >= 0
			if bound.Strict {
				holds = comparison > 0
			}
		}
		if !holds {
			return false
		}
	}
	return true
}

func evaluateIntegerAffineFactor(
	factor IntegerAffineFactor, value IntegerValue,
) IntegerValue {
	return AddIntegerValue(
		MultiplyIntegerValue(factor.Coefficient, value), factor.Offset,
	)
}
