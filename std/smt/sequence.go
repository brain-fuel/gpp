package smt

// IntegerSequenceValue is an exact ground Seq Int value. The first eight
// elements remain inline so ordinary constructed sequences need no result
// allocation.
type IntegerSequenceValue struct {
	count    int
	inline   [8]IntegerValue
	overflow []IntegerValue
}

// CompactIntegerSequence is an inline ground Seq Int term used by typed
// façades to avoid allocating a unit/concat AST during construction.
type CompactIntegerSequence struct {
	value IntegerSequenceValue
}

func (CompactIntegerSequence) isTerm(SequenceSort[IntSort]) {}

// EmptyCompactIntegerSequence constructs an empty compact sequence.
func EmptyCompactIntegerSequence() CompactIntegerSequence {
	return CompactIntegerSequence{}
}

// UnitCompactIntegerSequence constructs a one-element compact sequence.
func UnitCompactIntegerSequence(element IntegerValue) CompactIntegerSequence {
	var result CompactIntegerSequence
	result.value.append(element)
	return result
}

// AppendCompactIntegerSequence appends right to left.
func AppendCompactIntegerSequence(
	left,
	right CompactIntegerSequence,
) CompactIntegerSequence {
	left.value.appendSequence(right.value)
	return left
}

// Len reports the number of elements.
func (value IntegerSequenceValue) Len() int { return value.count }

// At returns the element at index.
func (value IntegerSequenceValue) At(index int) (IntegerValue, bool) {
	if index < 0 || index >= value.count {
		return IntegerValue{}, false
	}
	if value.overflow != nil {
		return value.overflow[index], true
	}
	return value.inline[index], true
}

func (value *IntegerSequenceValue) append(element IntegerValue) {
	if value.overflow != nil {
		value.overflow = append(value.overflow, element)
		value.count++
		return
	}
	if value.count < len(value.inline) {
		value.inline[value.count] = element
		value.count++
		return
	}
	value.overflow = make([]IntegerValue, value.count, value.count*2)
	copy(value.overflow, value.inline[:])
	value.overflow = append(value.overflow, element)
	value.count++
}

func (value *IntegerSequenceValue) appendSequence(other IntegerSequenceValue) {
	for index := 0; index < other.count; index++ {
		element, _ := other.At(index)
		value.append(element)
	}
}

func evaluateIntegerSequence(
	term Term[SequenceSort[IntSort]],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
) (IntegerSequenceValue, bool) {
	switch value := term.(type) {
	case CompactIntegerSequence:
		return value.value, true
	case sequenceEmpty[SequenceSort[IntSort]]:
		return IntegerSequenceValue{}, true
	case sequenceUnit[SequenceSort[IntSort]]:
		element, ok := value.value.(Term[IntSort])
		if !ok {
			return IntegerSequenceValue{}, false
		}
		evaluated, ok := evaluateInteger(element, booleans, integers, reals)
		if !ok {
			return IntegerSequenceValue{}, false
		}
		var result IntegerSequenceValue
		result.append(evaluated)
		return result, true
	case sequenceConcat[SequenceSort[IntSort]]:
		terms, ok := value.values.([]Term[SequenceSort[IntSort]])
		if !ok {
			return IntegerSequenceValue{}, false
		}
		var result IntegerSequenceValue
		for _, item := range terms {
			evaluated, ok := evaluateIntegerSequence(item, booleans, integers, reals)
			if !ok {
				return IntegerSequenceValue{}, false
			}
			result.appendSequence(evaluated)
		}
		return result, true
	default:
		return IntegerSequenceValue{}, false
	}
}

func equalIntegerSequences(left, right IntegerSequenceValue) bool {
	if left.count != right.count {
		return false
	}
	for index := 0; index < left.count; index++ {
		leftValue, _ := left.At(index)
		rightValue, _ := right.At(index)
		if CompareIntegerValue(leftValue, rightValue) != 0 {
			return false
		}
	}
	return true
}

func evaluateIntegerSequenceEquality(
	value Equal,
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
) (bool, bool) {
	left, ok := value.Left.(Term[SequenceSort[IntSort]])
	if !ok {
		return false, false
	}
	right, ok := value.Right.(Term[SequenceSort[IntSort]])
	if !ok {
		return false, false
	}
	leftValue, leftOK := evaluateIntegerSequence(left, booleans, integers, reals)
	rightValue, rightOK := evaluateIntegerSequence(right, booleans, integers, reals)
	return equalIntegerSequences(leftValue, rightValue), leftOK && rightOK
}

func containsIntegerSequenceTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case Equal:
		if _, ok := value.Left.(Term[SequenceSort[IntSort]]); ok {
			return true
		}
		return containsIntegerSequenceLength(value.Left) || containsIntegerSequenceLength(value.Right)
	case Less:
		return containsIntegerSequenceLength(value.Left) || containsIntegerSequenceLength(value.Right)
	case LessEqual:
		return containsIntegerSequenceLength(value.Left) || containsIntegerSequenceLength(value.Right)
	case Not:
		return containsIntegerSequenceTheory(value.Value)
	case And:
		for _, item := range value.Values {
			if containsIntegerSequenceTheory(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsIntegerSequenceTheory(item) {
				return true
			}
		}
	case TheoryConjunction:
		items, _ := value.atomValues()
		for _, item := range items {
			if containsIntegerSequenceTheory(item) {
				return true
			}
		}
	case Or:
		for _, item := range value.Values {
			if containsIntegerSequenceTheory(item) {
				return true
			}
		}
	case Implies:
		return containsIntegerSequenceTheory(value.Left) || containsIntegerSequenceTheory(value.Right)
	case Iff:
		return containsIntegerSequenceTheory(value.Left) || containsIntegerSequenceTheory(value.Right)
	case If[BoolSort]:
		return containsIntegerSequenceTheory(value.Condition) ||
			containsIntegerSequenceTheory(value.Then) ||
			containsIntegerSequenceTheory(value.Else)
	}
	return false
}

func containsIntegerSequenceLength(term any) bool {
	switch value := term.(type) {
	case sequenceLength:
		_, ok := value.value.(Term[SequenceSort[IntSort]])
		return ok
	case Add:
		for _, item := range value.Values {
			if containsIntegerSequenceLength(item) {
				return true
			}
		}
	case Subtract:
		return containsIntegerSequenceLength(value.Left) || containsIntegerSequenceLength(value.Right)
	case IntegerScale:
		return containsIntegerSequenceLength(value.Value)
	case If[IntSort]:
		return containsIntegerSequenceTheory(value.Condition) ||
			containsIntegerSequenceLength(value.Then) ||
			containsIntegerSequenceLength(value.Else)
	}
	return false
}

func solveGroundIntegerSequenceAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	found := false
	for _, assertion := range assertions {
		found = found || containsIntegerSequenceTheory(assertion)
	}
	if !found {
		return checkOutcome{}, false
	}
	for _, assertion := range assertions {
		value, ok := evaluateBool(assertion, booleanModel{}, integerModel{}, rationalModel{})
		if !ok {
			return checkOutcome{
				status: checkUnknown,
				reason: UnsupportedTheory{Name: "integer sequence expression outside the ground fragment"},
			}, true
		}
		if !value {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	return checkOutcome{status: checkSat}, true
}

// IntegerSequenceModelValue evaluates a ground integer sequence in model.
func IntegerSequenceModelValue(
	model Model,
	term Term[SequenceSort[IntSort]],
) (IntegerSequenceValue, bool) {
	return evaluateIntegerSequence(term, model.booleans, model.integers, model.reals)
}
