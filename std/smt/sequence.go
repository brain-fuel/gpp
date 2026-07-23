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
	case sequenceAt[SequenceSort[IntSort]]:
		sequence, ok := value.value.(Term[SequenceSort[IntSort]])
		if !ok {
			return IntegerSequenceValue{}, false
		}
		evaluated, ok := evaluateIntegerSequence(sequence, booleans, integers, reals)
		if !ok {
			return IntegerSequenceValue{}, false
		}
		index, ok := evaluateInteger(value.index, booleans, integers, reals)
		if !ok {
			return IntegerSequenceValue{}, false
		}
		position, fits := index.Int64()
		if !fits || position < 0 || position >= int64(evaluated.Len()) {
			return IntegerSequenceValue{}, true
		}
		element, _ := evaluated.At(int(position))
		var result IntegerSequenceValue
		result.append(element)
		return result, true
	case sequenceExtract[SequenceSort[IntSort]]:
		sequence, ok := value.value.(Term[SequenceSort[IntSort]])
		if !ok {
			return IntegerSequenceValue{}, false
		}
		evaluated, ok := evaluateIntegerSequence(sequence, booleans, integers, reals)
		if !ok {
			return IntegerSequenceValue{}, false
		}
		offset, offsetOK := evaluateInteger(value.offset, booleans, integers, reals)
		length, lengthOK := evaluateInteger(value.length, booleans, integers, reals)
		if !offsetOK || !lengthOK {
			return IntegerSequenceValue{}, false
		}
		start, startFits := offset.Int64()
		count, countFits := length.Int64()
		if !startFits || !countFits || start < 0 || count <= 0 || start >= int64(evaluated.Len()) {
			return IntegerSequenceValue{}, true
		}
		end := start + count
		if end < start || end > int64(evaluated.Len()) {
			end = int64(evaluated.Len())
		}
		return sliceIntegerSequence(evaluated, int(start), int(end)), true
	case sequenceReplace[SequenceSort[IntSort]]:
		sequence, sequenceOK := value.value.(Term[SequenceSort[IntSort]])
		source, sourceOK := value.source.(Term[SequenceSort[IntSort]])
		replacement, replacementOK := value.replacement.(Term[SequenceSort[IntSort]])
		if !sequenceOK || !sourceOK || !replacementOK {
			return IntegerSequenceValue{}, false
		}
		evaluated, valueOK := evaluateIntegerSequence(sequence, booleans, integers, reals)
		old, oldOK := evaluateIntegerSequence(source, booleans, integers, reals)
		next, nextOK := evaluateIntegerSequence(replacement, booleans, integers, reals)
		if !valueOK || !oldOK || !nextOK {
			return IntegerSequenceValue{}, false
		}
		position := findIntegerSubsequence(evaluated, old, 0)
		if position < 0 {
			return evaluated, true
		}
		var result IntegerSequenceValue
		result.appendSequence(sliceIntegerSequence(evaluated, 0, position))
		result.appendSequence(next)
		result.appendSequence(sliceIntegerSequence(evaluated, position+old.Len(), evaluated.Len()))
		return result, true
	default:
		return IntegerSequenceValue{}, false
	}
}

func sliceIntegerSequence(value IntegerSequenceValue, start, end int) IntegerSequenceValue {
	var result IntegerSequenceValue
	for index := start; index < end; index++ {
		element, _ := value.At(index)
		result.append(element)
	}
	return result
}

func findIntegerSubsequence(value, subsequence IntegerSequenceValue, offset int) int {
	if offset < 0 || offset > value.Len() {
		return -1
	}
	if subsequence.Len() == 0 {
		return offset
	}
	for start := offset; start+subsequence.Len() <= value.Len(); start++ {
		found := true
		for index := 0; index < subsequence.Len(); index++ {
			left, _ := value.At(start + index)
			right, _ := subsequence.At(index)
			if CompareIntegerValue(left, right) != 0 {
				found = false
				break
			}
		}
		if found {
			return start
		}
	}
	return -1
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

func evaluateIntegerSequencePredicate(
	term Term[BoolSort],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
) (bool, bool) {
	var leftTerm, rightTerm any
	var kind uint8
	switch value := term.(type) {
	case sequenceContains:
		leftTerm, rightTerm, kind = value.value, value.subsequence, 0
	case sequencePrefix:
		leftTerm, rightTerm, kind = value.value, value.prefix, 1
	case sequenceSuffix:
		leftTerm, rightTerm, kind = value.value, value.suffix, 2
	default:
		return false, false
	}
	left, leftOK := leftTerm.(Term[SequenceSort[IntSort]])
	right, rightOK := rightTerm.(Term[SequenceSort[IntSort]])
	if !leftOK || !rightOK {
		return false, false
	}
	value, valueOK := evaluateIntegerSequence(left, booleans, integers, reals)
	part, partOK := evaluateIntegerSequence(right, booleans, integers, reals)
	if !valueOK || !partOK {
		return false, false
	}
	switch kind {
	case 0:
		return findIntegerSubsequence(value, part, 0) >= 0, true
	case 1:
		return findIntegerSubsequence(value, part, 0) == 0, true
	default:
		return part.Len() <= value.Len() &&
			findIntegerSubsequence(value, part, value.Len()-part.Len()) == value.Len()-part.Len(), true
	}
}

func containsIntegerSequenceTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case sequenceContains, sequencePrefix, sequenceSuffix:
		return true
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
	case sequenceLength, sequenceIndexOf:
		var sequence any
		switch operation := value.(type) {
		case sequenceLength:
			sequence = operation.value
		case sequenceIndexOf:
			sequence = operation.value
		}
		_, ok := sequence.(Term[SequenceSort[IntSort]])
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
