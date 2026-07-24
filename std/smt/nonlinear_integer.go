package smt

import (
	"math"
	"math/big"
)

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

// IntegerAffineCubeRelation is the compact form (a*x+b)^3 = k (or != k).
type IntegerAffineCubeRelation struct {
	Factor  IntegerAffineFactor
	Target  IntegerValue
	Negated bool
}

func (IntegerAffineCubeRelation) isTerm(BoolSort) {}

// IntegerAffineCubeSystem is an allocation-free conjunction of affine cube
// relations for the exact nonlinear integer fragment.
type IntegerAffineCubeSystem struct {
	Count    int
	Inline   [4]IntegerAffineCubeRelation
	Overflow []IntegerAffineCubeRelation
}

func (IntegerAffineCubeSystem) isTerm(BoolSort) {}

// IntegerAffineCubeBound represents (a*x+b)^3 <(=) k when Lower is false
// and k <(=) (a*x+b)^3 when Lower is true.
type IntegerAffineCubeBound struct {
	Factor IntegerAffineFactor
	Bound  IntegerValue
	Lower  bool
	Strict bool
}

func (IntegerAffineCubeBound) isTerm(BoolSort) {}

// IntegerAffineCubeBoundSystem is an allocation-free conjunction of affine
// cube bounds.
type IntegerAffineCubeBoundSystem struct {
	Count    int
	Inline   [4]IntegerAffineCubeBound
	Overflow []IntegerAffineCubeBound
}

func (IntegerAffineCubeBoundSystem) isTerm(BoolSort) {}

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

// IntegerAffineProductBound represents
// (a*x+b)*(c*y+d) <(=) k when Lower is false and
// k <(=) (a*x+b)*(c*y+d) when Lower is true.
type IntegerAffineProductBound struct {
	Left, Right IntegerAffineFactor
	Bound       IntegerValue
	Lower       bool
	Strict      bool
}

func (IntegerAffineProductBound) isTerm(BoolSort) {}

// IntegerAffineProductBoundSystem is an allocation-free conjunction of
// affine bilinear bounds for the bounded nonlinear integer fragment.
type IntegerAffineProductBoundSystem struct {
	Count    int
	Inline   [4]IntegerAffineProductBound
	Overflow []IntegerAffineProductBound
}

func (IntegerAffineProductBoundSystem) isTerm(BoolSort) {}

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
	productBounds     [nonlinearIntegerRelationLimit]IntegerAffineProductBound
	cubeCount         int
	cubes             [nonlinearIntegerRelationLimit]IntegerAffineCubeRelation
	cubeBoundCount    int
	cubeBounds        [nonlinearIntegerRelationLimit]IntegerAffineCubeBound
	cubeHasLower      [nonlinearIntegerSymbolLimit]bool
	cubeHasUpper      [nonlinearIntegerSymbolLimit]bool
	cubeLower         [nonlinearIntegerSymbolLimit]IntegerValue
	cubeUpper         [nonlinearIntegerSymbolLimit]IntegerValue
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
		problem.productBoundCount == 0 && problem.cubeCount == 0 &&
		problem.cubeBoundCount == 0 {
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
	case IntegerAffineCubeRelation:
		value.Negated = value.Negated != negated
		return problem.addAffineCubeRelation(value)
	case IntegerAffineCubeSystem:
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
			if !problem.addAffineCubeRelation(relation) {
				return false
			}
		}
		return true
	case IntegerAffineCubeBound:
		if negated {
			value.Lower = !value.Lower
			value.Strict = !value.Strict
		}
		return problem.addAffineCubeBound(value)
	case IntegerAffineCubeBoundSystem:
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
			if !problem.addAffineCubeBound(bound) {
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
	case IntegerAffineProductBound:
		if negated {
			value.Lower = !value.Lower
			value.Strict = !value.Strict
		}
		return problem.addAffineProductBound(value)
	case IntegerAffineProductBoundSystem:
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
			if !problem.addAffineProductBound(bound) {
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
	factor, target, ok := nonlinearIntegerAffineCubeEquality(left, right)
	lower := false
	if !ok {
		factor, target, ok = nonlinearIntegerAffineCubeEquality(right, left)
		lower = true
	}
	if ok {
		if negated {
			lower = !lower
			strict = !strict
		}
		return problem.addAffineCubeBound(IntegerAffineCubeBound{
			Factor: factor, Bound: target, Lower: lower, Strict: strict,
		})
	}
	product, target, ok := nonlinearIntegerProductEquality(left, right)
	lower = false
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
	if !leftAffine || !rightAffine {
		return false
	}
	if negated {
		lower = !lower
		strict = !strict
	}
	return problem.addAffineProductBound(IntegerAffineProductBound{
		Left: leftFactor, Right: rightFactor,
		Bound: target, Lower: lower, Strict: strict,
	})
}

func (problem *nonlinearIntegerProblem) addProductBound(
	bound IntegerProductBound,
) bool {
	one := NewIntegerValue(1)
	return problem.addAffineProductBound(IntegerAffineProductBound{
		Left: IntegerAffineFactor{
			SymbolID: bound.LeftID, Coefficient: one,
		},
		Right: IntegerAffineFactor{
			SymbolID: bound.RightID, Coefficient: one,
		},
		Bound: bound.Bound, Lower: bound.Lower, Strict: bound.Strict,
	})
}

func (problem *nonlinearIntegerProblem) addAffineProductBound(
	bound IntegerAffineProductBound,
) bool {
	if problem.productBoundCount == len(problem.productBounds) {
		return false
	}
	left, leftAdded := problem.ensureSymbol(bound.Left.SymbolID)
	right, rightAdded := problem.ensureSymbol(bound.Right.SymbolID)
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
	for candidate := int64(-4); candidate <= 4; candidate++ {
		factorValue := NewIntegerValue(candidate)
		problem.addAffineFactorCandidate(left, bound.Left, factorValue)
		problem.addAffineFactorCandidate(right, bound.Right, factorValue)
		if candidate != 0 {
			quotient, _, ok := DivModIntegerValue(
				witness, factorValue,
			)
			if ok {
				for adjustment := int64(-2); adjustment <= 2; adjustment++ {
					near := AddIntegerValue(
						quotient, NewIntegerValue(adjustment),
					)
					problem.addAffineFactorCandidate(
						right, bound.Right, near,
					)
					problem.addAffineFactorCandidate(
						left, bound.Left, near,
					)
				}
			}
		}
	}
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
	cube, target, ok := nonlinearIntegerAffineCubeEquality(left, right)
	if !ok {
		cube, target, ok = nonlinearIntegerAffineCubeEquality(right, left)
	}
	if ok {
		return problem.addAffineCubeRelation(IntegerAffineCubeRelation{
			Factor: cube, Target: target, Negated: negated,
		})
	}
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

func (problem *nonlinearIntegerProblem) addAffineCubeRelation(
	value IntegerAffineCubeRelation,
) bool {
	if problem.cubeCount == len(problem.cubes) {
		return false
	}
	for _, existing := range problem.cubes[:problem.cubeCount] {
		if !equalIntegerAffineFactor(existing.Factor, value.Factor) {
			continue
		}
		sameTarget := CompareIntegerValue(existing.Target, value.Target) == 0
		if (!existing.Negated && !value.Negated && !sameTarget) ||
			(sameTarget && existing.Negated != value.Negated) {
			problem.impossible = true
			return true
		}
	}
	position, added := problem.ensureSymbol(value.Factor.SymbolID)
	if !added {
		return false
	}
	if value.Negated {
		// An affine cube with a nonzero coefficient is injective. For m
		// excluded targets, m+1 distinct variable values guarantee an escape.
		for candidate := 0; candidate <= problem.cubeCount+1; candidate++ {
			problem.candidates[position].add(
				NewIntegerValue(int64(candidate)),
			)
		}
	} else {
		root := integerCubeRoot(value.Target)
		cube := MultiplyIntegerValue(
			MultiplyIntegerValue(root, root), root,
		)
		if CompareIntegerValue(cube, value.Target) != 0 {
			problem.impossible = true
		} else {
			problem.addAffineFactorCandidate(position, value.Factor, root)
			problem.domainComplete[position] = true
		}
	}
	problem.cubes[problem.cubeCount] = value
	problem.cubeCount++
	return true
}

func (problem *nonlinearIntegerProblem) addAffineCubeBound(
	bound IntegerAffineCubeBound,
) bool {
	if problem.cubeBoundCount == len(problem.cubeBounds) {
		return false
	}
	position, added := problem.ensureSymbol(bound.Factor.SymbolID)
	if !added {
		return false
	}
	floor := integerCubeFloor(bound.Bound)
	exact := CompareIntegerValue(
		MultiplyIntegerValue(MultiplyIntegerValue(floor, floor), floor),
		bound.Bound,
	) == 0
	factorBoundary := floor
	if bound.Lower {
		if bound.Strict || !exact {
			factorBoundary = AddIntegerValue(
				factorBoundary, NewIntegerValue(1),
			)
		}
		problem.addAffineCubeVariableBound(
			position, bound.Factor, factorBoundary, true,
		)
	} else {
		if bound.Strict && exact {
			factorBoundary = AddIntegerValue(
				factorBoundary, NewIntegerValue(-1),
			)
		}
		problem.addAffineCubeVariableBound(
			position, bound.Factor, factorBoundary, false,
		)
	}
	problem.cubeBounds[problem.cubeBoundCount] = bound
	problem.cubeBoundCount++
	return true
}

func (problem *nonlinearIntegerProblem) addAffineCubeVariableBound(
	position int,
	factor IntegerAffineFactor,
	factorBoundary IntegerValue,
	lower bool,
) {
	numerator := AddIntegerValue(
		factorBoundary, NegateIntegerValue(factor.Offset),
	)
	coefficientPositive := CompareIntegerValue(
		factor.Coefficient, IntegerValue{},
	) > 0
	var variableBoundary IntegerValue
	if lower == coefficientPositive {
		variableBoundary = ceilDivideIntegerValue(
			numerator, factor.Coefficient,
		)
		if !problem.cubeHasLower[position] ||
			CompareIntegerValue(
				variableBoundary, problem.cubeLower[position],
			) > 0 {
			problem.cubeLower[position] = variableBoundary
			problem.cubeHasLower[position] = true
		}
	} else {
		variableBoundary = floorDivideIntegerValue(
			numerator, factor.Coefficient,
		)
		if !problem.cubeHasUpper[position] ||
			CompareIntegerValue(
				variableBoundary, problem.cubeUpper[position],
			) < 0 {
			problem.cubeUpper[position] = variableBoundary
			problem.cubeHasUpper[position] = true
		}
	}
	problem.candidates[position].add(variableBoundary)
	problem.candidates[position].add(AddIntegerValue(
		variableBoundary, NewIntegerValue(1),
	))
	problem.candidates[position].add(AddIntegerValue(
		variableBoundary, NewIntegerValue(-1),
	))
	problem.completeAffineCubeInterval(position)
}

func (problem *nonlinearIntegerProblem) completeAffineCubeInterval(
	position int,
) {
	if !problem.cubeHasLower[position] || !problem.cubeHasUpper[position] {
		return
	}
	lower, upper := problem.cubeLower[position], problem.cubeUpper[position]
	if CompareIntegerValue(lower, upper) > 0 {
		problem.impossible = true
		return
	}
	difference := AddIntegerValue(upper, NegateIntegerValue(lower))
	width, ok := difference.Int64()
	if !ok || width >= nonlinearIntegerCandidateLimit {
		return
	}
	for offset := int64(0); offset <= width; offset++ {
		problem.candidates[position].add(AddIntegerValue(
			lower, NewIntegerValue(offset),
		))
	}
	problem.domainComplete[position] = true
}

func floorDivideIntegerValue(
	numerator, denominator IntegerValue,
) IntegerValue {
	if left, leftOK := numerator.Int64(); leftOK {
		if right, rightOK := denominator.Int64(); rightOK &&
			right != 0 && (left != math.MinInt64 || right != -1) {
			quotient, remainder := left/right, left%right
			if remainder != 0 && (left < 0) != (right < 0) {
				quotient--
			}
			return NewIntegerValue(quotient)
		}
	}
	quotient := new(big.Int)
	remainder := new(big.Int)
	quotient.QuoRem(numerator.big(), denominator.big(), remainder)
	if remainder.Sign() != 0 &&
		(CompareIntegerValue(numerator, IntegerValue{}) < 0) !=
			(CompareIntegerValue(denominator, IntegerValue{}) < 0) {
		quotient.Sub(quotient, big.NewInt(1))
	}
	return integerValueFromBig(quotient)
}

func ceilDivideIntegerValue(
	numerator, denominator IntegerValue,
) IntegerValue {
	if left, leftOK := numerator.Int64(); leftOK {
		if right, rightOK := denominator.Int64(); rightOK &&
			right != 0 && (left != math.MinInt64 || right != -1) {
			quotient, remainder := left/right, left%right
			if remainder != 0 && (left < 0) == (right < 0) {
				quotient++
			}
			return NewIntegerValue(quotient)
		}
	}
	quotient := new(big.Int)
	remainder := new(big.Int)
	quotient.QuoRem(numerator.big(), denominator.big(), remainder)
	if remainder.Sign() != 0 &&
		(CompareIntegerValue(numerator, IntegerValue{}) < 0) ==
			(CompareIntegerValue(denominator, IntegerValue{}) < 0) {
		quotient.Add(quotient, big.NewInt(1))
	}
	return integerValueFromBig(quotient)
}

func integerCubeRoot(value IntegerValue) IntegerValue {
	negative := CompareIntegerValue(value, IntegerValue{}) < 0
	magnitude := absoluteIntegerValue(value)
	if inline, ok := magnitude.Int64(); ok {
		root := int64(math.Cbrt(float64(inline)))
		for root < inline && root+1 <= inline/(root+1)/(root+1) {
			root++
		}
		for root > 0 && root > inline/root/root {
			root--
		}
		if negative {
			root = -root
		}
		return NewIntegerValue(root)
	}
	target := magnitude.big()
	low := new(big.Int)
	high := new(big.Int).Lsh(big.NewInt(1), uint((target.BitLen()+2)/3))
	one := big.NewInt(1)
	for new(big.Int).Sub(high, low).Cmp(one) > 0 {
		middle := new(big.Int).Add(low, high)
		middle.Rsh(middle, 1)
		cube := new(big.Int).Mul(middle, middle)
		cube.Mul(cube, middle)
		if cube.Cmp(target) <= 0 {
			low = middle
		} else {
			high = middle
		}
	}
	if negative {
		low.Neg(low)
	}
	return integerValueFromBig(low)
}

func integerCubeFloor(value IntegerValue) IntegerValue {
	root := integerCubeRoot(value)
	cube := MultiplyIntegerValue(
		MultiplyIntegerValue(root, root), root,
	)
	if CompareIntegerValue(cube, value) > 0 {
		root = AddIntegerValue(root, NewIntegerValue(-1))
	}
	return root
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

func nonlinearIntegerAffineCubeEquality(
	cubeTerm, targetTerm any,
) (IntegerAffineFactor, IntegerValue, bool) {
	cubeExpression, ok := cubeTerm.(Term[IntSort])
	if !ok {
		return IntegerAffineFactor{}, IntegerValue{}, false
	}
	factor, ok := nonlinearIntegerAffineCube(cubeExpression)
	if !ok {
		return IntegerAffineFactor{}, IntegerValue{}, false
	}
	targetExpression, ok := targetTerm.(Term[IntSort])
	if !ok {
		return IntegerAffineFactor{}, IntegerValue{}, false
	}
	target, ok := evaluateInteger(
		targetExpression,
		booleanModel{}, integerModel{}, rationalModel{},
	)
	return factor, target, ok
}

func nonlinearIntegerAffineCube(
	term Term[IntSort],
) (IntegerAffineFactor, bool) {
	product, ok := term.(IntegerMultiply)
	if !ok {
		return IntegerAffineFactor{}, false
	}
	for _, orientation := range [2]struct {
		factor Term[IntSort]
		square Term[IntSort]
	}{
		{factor: product.Left, square: product.Right},
		{factor: product.Right, square: product.Left},
	} {
		factor, factorOK := nonlinearIntegerAffineFactor(orientation.factor)
		square, squareOK := orientation.square.(IntegerMultiply)
		if !factorOK || !squareOK {
			continue
		}
		left, leftOK := nonlinearIntegerAffineFactor(square.Left)
		right, rightOK := nonlinearIntegerAffineFactor(square.Right)
		if leftOK && rightOK &&
			equalIntegerAffineFactor(factor, left) &&
			equalIntegerAffineFactor(factor, right) {
			return factor, true
		}
	}
	return IntegerAffineFactor{}, false
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
		left := problem.symbolPosition(bound.Left.SymbolID)
		right := problem.symbolPosition(bound.Right.SymbolID)
		if left < 0 || right < 0 || !assigned[left] || !assigned[right] {
			continue
		}
		comparison := CompareIntegerValue(
			MultiplyIntegerValue(
				evaluateIntegerAffineFactor(bound.Left, values[left]),
				evaluateIntegerAffineFactor(bound.Right, values[right]),
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
	for _, relation := range problem.cubes[:problem.cubeCount] {
		position := problem.symbolPosition(relation.Factor.SymbolID)
		if position < 0 || !assigned[position] {
			continue
		}
		factor := evaluateIntegerAffineFactor(
			relation.Factor, values[position],
		)
		cube := MultiplyIntegerValue(
			MultiplyIntegerValue(factor, factor), factor,
		)
		holds := CompareIntegerValue(cube, relation.Target) == 0
		if holds == relation.Negated {
			return false
		}
	}
	for _, bound := range problem.cubeBounds[:problem.cubeBoundCount] {
		position := problem.symbolPosition(bound.Factor.SymbolID)
		if position < 0 || !assigned[position] {
			continue
		}
		factor := evaluateIntegerAffineFactor(
			bound.Factor, values[position],
		)
		cube := MultiplyIntegerValue(
			MultiplyIntegerValue(factor, factor), factor,
		)
		comparison := CompareIntegerValue(cube, bound.Bound)
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
