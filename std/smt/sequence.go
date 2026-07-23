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

type integerSequenceModelEntry struct {
	id    int
	value IntegerSequenceValue
}

type integerSequenceModel struct {
	count    int
	inline   [4]integerSequenceModelEntry
	overflow map[int]IntegerSequenceValue
}

type integerSequenceAliasEntry struct {
	id     int
	parent int
}

type integerSequenceAliases struct {
	count    int
	inline   [8]integerSequenceAliasEntry
	overflow map[int]int
}

func (aliases *integerSequenceAliases) parent(id int) (int, bool) {
	for index := 0; index < aliases.count && index < len(aliases.inline); index++ {
		if aliases.inline[index].id == id {
			return aliases.inline[index].parent, true
		}
	}
	parent, ok := aliases.overflow[id]
	return parent, ok
}

func (aliases *integerSequenceAliases) ensure(id int) {
	if _, ok := aliases.parent(id); ok {
		return
	}
	if aliases.count < len(aliases.inline) {
		aliases.inline[aliases.count] = integerSequenceAliasEntry{id: id, parent: id}
		aliases.count++
		return
	}
	if aliases.overflow == nil {
		aliases.overflow = make(map[int]int)
	}
	aliases.overflow[id] = id
	aliases.count++
}

func (aliases *integerSequenceAliases) setParent(id, parent int) {
	for index := 0; index < aliases.count && index < len(aliases.inline); index++ {
		if aliases.inline[index].id == id {
			aliases.inline[index].parent = parent
			return
		}
	}
	aliases.overflow[id] = parent
}

func (aliases *integerSequenceAliases) root(id int) int {
	parent, ok := aliases.parent(id)
	if !ok {
		return id
	}
	for parent != id {
		id = parent
		parent, _ = aliases.parent(id)
	}
	return id
}

func (aliases *integerSequenceAliases) union(left, right int) {
	aliases.ensure(left)
	aliases.ensure(right)
	left, right = aliases.root(left), aliases.root(right)
	if left == right {
		return
	}
	if right < left {
		left, right = right, left
	}
	aliases.setParent(right, left)
}

type integerSequenceRequirements struct {
	prefix      IntegerSequenceValue
	suffix      IntegerSequenceValue
	exactLength int
	minLength   int
	maxLength   int
	hasPrefix   bool
	hasSuffix   bool
	hasLength   bool
	hasMin      bool
	hasMax      bool
	contains    [4]IntegerSequenceValue
	overflow    []IntegerSequenceValue
	containment int
}

const maximumConstructedIntegerSequenceLength = 4096

type integerSequenceRequirementEntry struct {
	id           int
	requirements integerSequenceRequirements
}

type integerSequenceRequirementSet struct {
	count            int
	inline           [4]integerSequenceRequirementEntry
	overflow         map[int]*integerSequenceRequirements
	relations        [4]integerSequenceLengthRelation
	relationOverflow []integerSequenceLengthRelation
	relationCount    int
}

type integerSequenceLengthRelation struct {
	ids          [8]int
	coefficients [8]IntegerValue
	count        int
	constant     IntegerValue
	equality     bool
}

func (set *integerSequenceRequirementSet) addRelation(
	relation integerSequenceLengthRelation,
) {
	if set.relationCount < len(set.relations) {
		set.relations[set.relationCount] = relation
	} else {
		set.relationOverflow = append(set.relationOverflow, relation)
	}
	set.relationCount++
}

func (set *integerSequenceRequirementSet) relationAt(
	index int,
) integerSequenceLengthRelation {
	if index < len(set.relations) {
		return set.relations[index]
	}
	return set.relationOverflow[index-len(set.relations)]
}

func (model integerSequenceModel) lookup(id int) (IntegerSequenceValue, bool) {
	for index := 0; index < model.count && index < len(model.inline); index++ {
		if model.inline[index].id == id {
			return model.inline[index].value, true
		}
	}
	value, ok := model.overflow[id]
	return value, ok
}

func (model *integerSequenceModel) set(id int, value IntegerSequenceValue) bool {
	for index := 0; index < model.count && index < len(model.inline); index++ {
		if model.inline[index].id == id {
			if !equalIntegerSequences(model.inline[index].value, value) {
				return false
			}
			return true
		}
	}
	if existing, ok := model.overflow[id]; ok {
		return equalIntegerSequences(existing, value)
	}
	if model.count < len(model.inline) {
		model.inline[model.count] = integerSequenceModelEntry{id: id, value: value}
		model.count++
		return true
	}
	if model.overflow == nil {
		model.overflow = make(map[int]IntegerSequenceValue)
	}
	model.overflow[id] = value
	model.count++
	return true
}

func (set *integerSequenceRequirementSet) forSymbol(id int) *integerSequenceRequirements {
	for index := 0; index < set.count && index < len(set.inline); index++ {
		if set.inline[index].id == id {
			return &set.inline[index].requirements
		}
	}
	if requirements := set.overflow[id]; requirements != nil {
		return requirements
	}
	if set.count < len(set.inline) {
		set.inline[set.count].id = id
		set.count++
		return &set.inline[set.count-1].requirements
	}
	if set.overflow == nil {
		set.overflow = make(map[int]*integerSequenceRequirements)
	}
	requirements := new(integerSequenceRequirements)
	set.overflow[id] = requirements
	set.count++
	return requirements
}

func (requirements *integerSequenceRequirements) addContainment(value IntegerSequenceValue) {
	for index := 0; index < requirements.containment; index++ {
		existing := requirements.containmentAt(index)
		if equalIntegerSequences(existing, value) {
			return
		}
	}
	if requirements.containment < len(requirements.contains) {
		requirements.contains[requirements.containment] = value
	} else {
		requirements.overflow = append(requirements.overflow, value)
	}
	requirements.containment++
}

func (requirements integerSequenceRequirements) containmentAt(index int) IntegerSequenceValue {
	if index < len(requirements.contains) {
		return requirements.contains[index]
	}
	return requirements.overflow[index-len(requirements.contains)]
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
	return evaluateIntegerSequenceWithModel(
		term, booleans, integers, reals, integerSequenceModel{},
	)
}

func evaluateIntegerSequenceWithModel(
	term Term[SequenceSort[IntSort]],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
	sequences integerSequenceModel,
) (IntegerSequenceValue, bool) {
	switch value := term.(type) {
	case CompactIntegerSequence:
		return value.value, true
	case sequenceEmpty[SequenceSort[IntSort]]:
		return IntegerSequenceValue{}, true
	case sequenceSymbol[SequenceSort[IntSort]]:
		return sequences.lookup(value.iD)
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
			evaluated, ok := evaluateIntegerSequenceWithModel(item, booleans, integers, reals, sequences)
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
		evaluated, ok := evaluateIntegerSequenceWithModel(sequence, booleans, integers, reals, sequences)
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
		evaluated, ok := evaluateIntegerSequenceWithModel(sequence, booleans, integers, reals, sequences)
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
		evaluated, valueOK := evaluateIntegerSequenceWithModel(sequence, booleans, integers, reals, sequences)
		old, oldOK := evaluateIntegerSequenceWithModel(source, booleans, integers, reals, sequences)
		next, nextOK := evaluateIntegerSequenceWithModel(replacement, booleans, integers, reals, sequences)
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
	return evaluateIntegerSequenceEqualityWithModel(
		value, booleans, integers, reals, integerSequenceModel{},
	)
}

func evaluateIntegerSequenceEqualityWithModel(
	value Equal,
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
	sequences integerSequenceModel,
) (bool, bool) {
	left, ok := value.Left.(Term[SequenceSort[IntSort]])
	if !ok {
		return false, false
	}
	right, ok := value.Right.(Term[SequenceSort[IntSort]])
	if !ok {
		return false, false
	}
	leftValue, leftOK := evaluateIntegerSequenceWithModel(left, booleans, integers, reals, sequences)
	rightValue, rightOK := evaluateIntegerSequenceWithModel(right, booleans, integers, reals, sequences)
	return equalIntegerSequences(leftValue, rightValue), leftOK && rightOK
}

func evaluateIntegerSequencePredicate(
	term Term[BoolSort],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
) (bool, bool) {
	return evaluateIntegerSequencePredicateWithModel(
		term, booleans, integers, reals, integerSequenceModel{},
	)
}

func evaluateIntegerSequencePredicateWithModel(
	term Term[BoolSort],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
	sequences integerSequenceModel,
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
	value, valueOK := evaluateIntegerSequenceWithModel(left, booleans, integers, reals, sequences)
	part, partOK := evaluateIntegerSequenceWithModel(right, booleans, integers, reals, sequences)
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

func evaluateIntegerWithSequences(
	term Term[IntSort],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
	bitVectors bitVectorModel,
	sequences integerSequenceModel,
) (IntegerValue, bool) {
	switch value := term.(type) {
	case sequenceLength:
		sequence, ok := value.value.(Term[SequenceSort[IntSort]])
		if !ok {
			return IntegerValue{}, false
		}
		evaluated, ok := evaluateIntegerSequenceWithModel(
			sequence, booleans, integers, reals, sequences,
		)
		if !ok {
			return IntegerValue{}, false
		}
		return NewIntegerValue(int64(evaluated.Len())), true
	case sequenceIndexOf:
		sequence, sequenceOK := value.value.(Term[SequenceSort[IntSort]])
		subsequence, subsequenceOK := value.subsequence.(Term[SequenceSort[IntSort]])
		if !sequenceOK || !subsequenceOK {
			return IntegerValue{}, false
		}
		evaluated, valueOK := evaluateIntegerSequenceWithModel(
			sequence, booleans, integers, reals, sequences,
		)
		part, partOK := evaluateIntegerSequenceWithModel(
			subsequence, booleans, integers, reals, sequences,
		)
		offset, offsetOK := evaluateIntegerWithSequences(
			value.offset, booleans, integers, reals, bitVectors, sequences,
		)
		if !valueOK || !partOK || !offsetOK {
			return IntegerValue{}, false
		}
		start, fits := offset.Int64()
		if !fits || start < 0 || start > int64(evaluated.Len()) {
			return NewIntegerValue(-1), true
		}
		return NewIntegerValue(int64(findIntegerSubsequence(evaluated, part, int(start)))), true
	case Add:
		result := IntegerValue{}
		for _, item := range value.Values {
			next, ok := evaluateIntegerWithSequences(
				item, booleans, integers, reals, bitVectors, sequences,
			)
			if !ok {
				return IntegerValue{}, false
			}
			result = AddIntegerValue(result, next)
		}
		return result, true
	case Subtract:
		left, leftOK := evaluateIntegerWithSequences(
			value.Left, booleans, integers, reals, bitVectors, sequences,
		)
		right, rightOK := evaluateIntegerWithSequences(
			value.Right, booleans, integers, reals, bitVectors, sequences,
		)
		return SubIntegerValue(left, right), leftOK && rightOK
	case IntegerScale:
		evaluated, ok := evaluateIntegerWithSequences(
			value.Value, booleans, integers, reals, bitVectors, sequences,
		)
		if !ok {
			return IntegerValue{}, false
		}
		return MultiplyIntegerValue(value.Coefficient, evaluated), true
	case If[IntSort]:
		condition, ok := evaluateBoolWithIntegerSequences(
			value.Condition, booleans, integers, reals, sequences,
		)
		if !ok {
			return IntegerValue{}, false
		}
		if condition {
			return evaluateIntegerWithSequences(
				value.Then, booleans, integers, reals, bitVectors, sequences,
			)
		}
		return evaluateIntegerWithSequences(
			value.Else, booleans, integers, reals, bitVectors, sequences,
		)
	default:
		return evaluateIntegerWithBitVectors(term, booleans, integers, reals, bitVectors)
	}
}

func evaluateBoolWithIntegerSequences(
	term Term[BoolSort],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
	sequences integerSequenceModel,
) (bool, bool) {
	switch value := term.(type) {
	case Equal:
		if _, ok := value.Left.(Term[SequenceSort[IntSort]]); ok {
			return evaluateIntegerSequenceEqualityWithModel(
				value, booleans, integers, reals, sequences,
			)
		}
		if containsIntegerSequenceLength(value.Left) || containsIntegerSequenceLength(value.Right) {
			left, leftOK := value.Left.(Term[IntSort])
			right, rightOK := value.Right.(Term[IntSort])
			if !leftOK || !rightOK {
				return false, false
			}
			leftValue, leftOK := evaluateIntegerWithSequences(
				left, booleans, integers, reals, bitVectorModel{}, sequences,
			)
			rightValue, rightOK := evaluateIntegerWithSequences(
				right, booleans, integers, reals, bitVectorModel{}, sequences,
			)
			return CompareIntegerValue(leftValue, rightValue) == 0, leftOK && rightOK
		}
	case sequenceContains, sequencePrefix, sequenceSuffix:
		return evaluateIntegerSequencePredicateWithModel(
			term, booleans, integers, reals, sequences,
		)
	case Less:
		left, leftOK := evaluateIntegerWithSequences(
			value.Left, booleans, integers, reals, bitVectorModel{}, sequences,
		)
		right, rightOK := evaluateIntegerWithSequences(
			value.Right, booleans, integers, reals, bitVectorModel{}, sequences,
		)
		return CompareIntegerValue(left, right) < 0, leftOK && rightOK
	case LessEqual:
		left, leftOK := evaluateIntegerWithSequences(
			value.Left, booleans, integers, reals, bitVectorModel{}, sequences,
		)
		right, rightOK := evaluateIntegerWithSequences(
			value.Right, booleans, integers, reals, bitVectorModel{}, sequences,
		)
		return CompareIntegerValue(left, right) <= 0, leftOK && rightOK
	case Not:
		result, ok := evaluateBoolWithIntegerSequences(
			value.Value, booleans, integers, reals, sequences,
		)
		return !result, ok
	case And:
		for _, item := range value.Values {
			result, ok := evaluateBoolWithIntegerSequences(
				item, booleans, integers, reals, sequences,
			)
			if !ok || !result {
				return result, ok
			}
		}
		return true, true
	case BooleanConjunction:
		items, negated := value.values()
		for index, item := range items {
			result, ok := evaluateBoolWithIntegerSequences(
				item, booleans, integers, reals, sequences,
			)
			if !ok || result == negated[index] {
				return false, ok
			}
		}
		return true, true
	case Or:
		for _, item := range value.Values {
			result, ok := evaluateBoolWithIntegerSequences(
				item, booleans, integers, reals, sequences,
			)
			if !ok {
				return false, false
			}
			if result {
				return true, true
			}
		}
		return false, true
	case Implies:
		left, leftOK := evaluateBoolWithIntegerSequences(
			value.Left, booleans, integers, reals, sequences,
		)
		right, rightOK := evaluateBoolWithIntegerSequences(
			value.Right, booleans, integers, reals, sequences,
		)
		return !left || right, leftOK && rightOK
	case Iff:
		left, leftOK := evaluateBoolWithIntegerSequences(
			value.Left, booleans, integers, reals, sequences,
		)
		right, rightOK := evaluateBoolWithIntegerSequences(
			value.Right, booleans, integers, reals, sequences,
		)
		return left == right, leftOK && rightOK
	case If[BoolSort]:
		condition, ok := evaluateBoolWithIntegerSequences(
			value.Condition, booleans, integers, reals, sequences,
		)
		if !ok {
			return false, false
		}
		if condition {
			return evaluateBoolWithIntegerSequences(
				value.Then, booleans, integers, reals, sequences,
			)
		}
		return evaluateBoolWithIntegerSequences(
			value.Else, booleans, integers, reals, sequences,
		)
	}
	return evaluateBool(term, booleans, integers, reals)
}

func bindGroundIntegerSequenceAssignments(
	term Term[BoolSort],
	model *integerSequenceModel,
	aliases *integerSequenceAliases,
) (bool, bool) {
	switch value := term.(type) {
	case Equal:
		left, leftSymbol := integerSequenceSymbolID(value.Left)
		right, rightSymbol := integerSequenceSymbolID(value.Right)
		if leftSymbol {
			left = aliases.root(left)
		}
		if rightSymbol {
			right = aliases.root(right)
		}
		if leftSymbol {
			sequence, ok := value.Right.(Term[SequenceSort[IntSort]])
			if !ok || rightSymbol {
				return false, false
			}
			evaluated, ok := evaluateIntegerSequenceWithModel(
				sequence, booleanModel{}, integerModel{}, rationalModel{}, *model,
			)
			if !ok {
				return false, false
			}
			return model.set(left, evaluated), true
		}
		if rightSymbol {
			sequence, ok := value.Left.(Term[SequenceSort[IntSort]])
			if !ok {
				return false, false
			}
			evaluated, ok := evaluateIntegerSequenceWithModel(
				sequence, booleanModel{}, integerModel{}, rationalModel{}, *model,
			)
			if !ok {
				return false, false
			}
			return model.set(right, evaluated), true
		}
	case And:
		for _, item := range value.Values {
			consistent, bound := bindGroundIntegerSequenceAssignments(item, model, aliases)
			if bound && !consistent {
				return false, true
			}
		}
	case BooleanConjunction:
		items, negated := value.values()
		for index, item := range items {
			if negated[index] {
				continue
			}
			consistent, bound := bindGroundIntegerSequenceAssignments(item, model, aliases)
			if bound && !consistent {
				return false, true
			}
		}
	}
	return true, false
}

func collectIntegerSequenceAliases(
	term Term[BoolSort],
	aliases *integerSequenceAliases,
) {
	switch value := term.(type) {
	case Equal:
		left, leftOK := integerSequenceSymbolID(value.Left)
		right, rightOK := integerSequenceSymbolID(value.Right)
		if leftOK && rightOK {
			aliases.union(left, right)
		}
	case And:
		for _, item := range value.Values {
			collectIntegerSequenceAliases(item, aliases)
		}
	case BooleanConjunction:
		items, negated := value.values()
		for index, item := range items {
			if !negated[index] {
				collectIntegerSequenceAliases(item, aliases)
			}
		}
	}
}

func expandIntegerSequenceAliases(
	aliases *integerSequenceAliases,
	model *integerSequenceModel,
) bool {
	for index := 0; index < aliases.count && index < len(aliases.inline); index++ {
		id := aliases.inline[index].id
		if value, ok := model.lookup(aliases.root(id)); ok && !model.set(id, value) {
			return false
		}
	}
	for id := range aliases.overflow {
		if value, ok := model.lookup(aliases.root(id)); ok && !model.set(id, value) {
			return false
		}
	}
	return true
}

func integerSequenceSymbolID(term any) (int, bool) {
	value, ok := term.(sequenceSymbol[SequenceSort[IntSort]])
	return value.iD, ok
}

func integerSequenceStartsWith(
	value,
	prefix IntegerSequenceValue,
) bool {
	return prefix.Len() <= value.Len() &&
		findIntegerSubsequence(value, prefix, 0) == 0
}

func integerSequenceEndsWith(
	value,
	suffix IntegerSequenceValue,
) bool {
	return suffix.Len() <= value.Len() &&
		findIntegerSubsequence(value, suffix, value.Len()-suffix.Len()) ==
			value.Len()-suffix.Len()
}

func addIntegerSequencePrefix(
	requirements *integerSequenceRequirements,
	prefix IntegerSequenceValue,
) bool {
	if !requirements.hasPrefix {
		requirements.prefix = prefix
		requirements.hasPrefix = true
		return true
	}
	if integerSequenceStartsWith(prefix, requirements.prefix) {
		requirements.prefix = prefix
		return true
	}
	return integerSequenceStartsWith(requirements.prefix, prefix)
}

func addIntegerSequenceSuffix(
	requirements *integerSequenceRequirements,
	suffix IntegerSequenceValue,
) bool {
	if !requirements.hasSuffix {
		requirements.suffix = suffix
		requirements.hasSuffix = true
		return true
	}
	if integerSequenceEndsWith(suffix, requirements.suffix) {
		requirements.suffix = suffix
		return true
	}
	return integerSequenceEndsWith(requirements.suffix, suffix)
}

func addIntegerSequenceExactLength(
	requirements *integerSequenceRequirements,
	length int,
) bool {
	if requirements.hasMin && length < requirements.minLength {
		return false
	}
	if requirements.hasMax && length > requirements.maxLength {
		return false
	}
	if !requirements.hasLength {
		requirements.exactLength = length
		requirements.hasLength = true
		requirements.minLength = length
		requirements.maxLength = length
		requirements.hasMin = true
		requirements.hasMax = true
		return true
	}
	return requirements.exactLength == length
}

func addIntegerSequenceMinimumLength(
	requirements *integerSequenceRequirements,
	length int,
) bool {
	if length < 0 {
		length = 0
	}
	if !requirements.hasMin || length > requirements.minLength {
		requirements.minLength = length
		requirements.hasMin = true
	}
	return !requirements.hasMax || requirements.minLength <= requirements.maxLength
}

func addIntegerSequenceMaximumLength(
	requirements *integerSequenceRequirements,
	length int,
) bool {
	if !requirements.hasMax || length < requirements.maxLength {
		requirements.maxLength = length
		requirements.hasMax = true
	}
	return requirements.maxLength >= 0 &&
		(!requirements.hasMin || requirements.minLength <= requirements.maxLength)
}

func symbolicIntegerSequenceLength(term any) (int, bool) {
	length, ok := term.(sequenceLength)
	if !ok {
		return 0, false
	}
	sequence, ok := length.value.(Term[SequenceSort[IntSort]])
	if !ok {
		return 0, false
	}
	return integerSequenceSymbolID(sequence)
}

type integerSequenceLengthAffine struct {
	id          int
	coefficient IntegerValue
	constant    IntegerValue
	hasSymbol   bool
	valid       bool
}

func containsIntegerSequenceAffineLength(term any) bool {
	switch value := term.(type) {
	case sequenceLength:
		_, ok := value.value.(Term[SequenceSort[IntSort]])
		return ok
	case Add:
		for _, item := range value.Values {
			if containsIntegerSequenceAffineLength(item) {
				return true
			}
		}
	case Subtract:
		return containsIntegerSequenceAffineLength(value.Left) ||
			containsIntegerSequenceAffineLength(value.Right)
	case IntegerScale:
		return containsIntegerSequenceAffineLength(value.Value)
	}
	return false
}

func accumulateIntegerSequenceLengthAffine(
	term Term[IntSort],
	multiplier IntegerValue,
	form *integerSequenceLengthAffine,
) {
	if !form.valid {
		return
	}
	if id, ok := symbolicIntegerSequenceLength(term); ok {
		if form.hasSymbol && form.id != id {
			form.valid = false
			return
		}
		form.id = id
		form.hasSymbol = true
		form.coefficient = AddIntegerValue(form.coefficient, multiplier)
		return
	}
	if containsIntegerSequenceAffineLength(term) {
		if value, ok := evaluateIntegerWithSequences(
			term,
			booleanModel{},
			integerModel{},
			rationalModel{},
			bitVectorModel{},
			integerSequenceModel{},
		); ok {
			form.constant = AddIntegerValue(
				form.constant,
				MultiplyIntegerValue(multiplier, value),
			)
			return
		}
	}
	switch value := term.(type) {
	case Integer:
		form.constant = AddIntegerValue(
			form.constant,
			MultiplyIntegerValue(multiplier, NewIntegerValue(value.Value)),
		)
	case integerExact[IntSort]:
		form.constant = AddIntegerValue(
			form.constant,
			MultiplyIntegerValue(multiplier, value.value),
		)
	case Add:
		for _, item := range value.Values {
			accumulateIntegerSequenceLengthAffine(item, multiplier, form)
		}
	case Subtract:
		accumulateIntegerSequenceLengthAffine(value.Left, multiplier, form)
		accumulateIntegerSequenceLengthAffine(
			value.Right, NegateIntegerValue(multiplier), form,
		)
	case IntegerScale:
		accumulateIntegerSequenceLengthAffine(
			value.Value,
			MultiplyIntegerValue(multiplier, value.Coefficient),
			form,
		)
	default:
		form.valid = false
	}
}

func normalizeIntegerSequenceLengthAffine(
	left,
	right Term[IntSort],
) integerSequenceLengthAffine {
	form := integerSequenceLengthAffine{valid: true}
	accumulateIntegerSequenceLengthAffine(left, NewIntegerValue(1), &form)
	accumulateIntegerSequenceLengthAffine(right, NewIntegerValue(-1), &form)
	return form
}

type integerSequenceLengthMultiAffine struct {
	ids          [8]int
	coefficients [8]IntegerValue
	count        int
	constant     IntegerValue
	valid        bool
}

func (form *integerSequenceLengthMultiAffine) add(
	id int,
	coefficient IntegerValue,
) {
	for index := 0; index < form.count; index++ {
		if form.ids[index] == id {
			form.coefficients[index] = AddIntegerValue(
				form.coefficients[index], coefficient,
			)
			return
		}
	}
	if form.count == len(form.ids) {
		form.valid = false
		return
	}
	form.ids[form.count] = id
	form.coefficients[form.count] = coefficient
	form.count++
}

func accumulateIntegerSequenceLengthMultiAffine(
	term Term[IntSort],
	multiplier IntegerValue,
	form *integerSequenceLengthMultiAffine,
	aliases *integerSequenceAliases,
) {
	if !form.valid {
		return
	}
	if id, ok := symbolicIntegerSequenceLength(term); ok {
		form.add(aliases.root(id), multiplier)
		return
	}
	if containsIntegerSequenceAffineLength(term) {
		if value, ok := evaluateIntegerWithSequences(
			term,
			booleanModel{},
			integerModel{},
			rationalModel{},
			bitVectorModel{},
			integerSequenceModel{},
		); ok {
			form.constant = AddIntegerValue(
				form.constant, MultiplyIntegerValue(multiplier, value),
			)
			return
		}
	}
	switch value := term.(type) {
	case Integer:
		form.constant = AddIntegerValue(
			form.constant,
			MultiplyIntegerValue(multiplier, NewIntegerValue(value.Value)),
		)
	case integerExact[IntSort]:
		form.constant = AddIntegerValue(
			form.constant,
			MultiplyIntegerValue(multiplier, value.value),
		)
	case Add:
		for _, item := range value.Values {
			accumulateIntegerSequenceLengthMultiAffine(
				item, multiplier, form, aliases,
			)
		}
	case Subtract:
		accumulateIntegerSequenceLengthMultiAffine(
			value.Left, multiplier, form, aliases,
		)
		accumulateIntegerSequenceLengthMultiAffine(
			value.Right, NegateIntegerValue(multiplier), form, aliases,
		)
	case IntegerScale:
		accumulateIntegerSequenceLengthMultiAffine(
			value.Value,
			MultiplyIntegerValue(multiplier, value.Coefficient),
			form,
			aliases,
		)
	default:
		form.valid = false
	}
}

func normalizeIntegerSequenceLengthMultiAffine(
	left,
	right Term[IntSort],
	aliases *integerSequenceAliases,
) integerSequenceLengthMultiAffine {
	form := integerSequenceLengthMultiAffine{valid: true}
	accumulateIntegerSequenceLengthMultiAffine(
		left, NewIntegerValue(1), &form, aliases,
	)
	accumulateIntegerSequenceLengthMultiAffine(
		right, NewIntegerValue(-1), &form, aliases,
	)
	compacted := integerSequenceLengthMultiAffine{
		constant: form.constant,
		valid:    form.valid,
	}
	for index := 0; index < form.count; index++ {
		if CompareIntegerValue(form.coefficients[index], IntegerValue{}) != 0 {
			compacted.add(form.ids[index], form.coefficients[index])
		}
	}
	return compacted
}

func greatestCommonIntegerSequenceLengthCoefficient(
	form integerSequenceLengthMultiAffine,
) IntegerValue {
	divisor := form.coefficients[0]
	if CompareIntegerValue(divisor, IntegerValue{}) < 0 {
		divisor = NegateIntegerValue(divisor)
	}
	for index := 1; index < form.count; index++ {
		coefficient := form.coefficients[index]
		if CompareIntegerValue(coefficient, IntegerValue{}) < 0 {
			coefficient = NegateIntegerValue(coefficient)
		}
		for CompareIntegerValue(coefficient, IntegerValue{}) != 0 {
			_, remainder, _ := DivModIntegerValue(divisor, coefficient)
			divisor, coefficient = coefficient, remainder
		}
	}
	return divisor
}

func applyIntegerSequenceMinimumValue(
	requirements *integerSequenceRequirements,
	value IntegerValue,
) (bool, bool) {
	length, fits := value.Int64()
	if !fits || length > maximumConstructedIntegerSequenceLength {
		return true, false
	}
	return addIntegerSequenceMinimumLength(requirements, int(length)), true
}

func applyIntegerSequenceMaximumValue(
	requirements *integerSequenceRequirements,
	value IntegerValue,
) (bool, bool) {
	length, fits := value.Int64()
	if !fits {
		if CompareIntegerValue(value, IntegerValue{}) > 0 {
			return true, true
		}
		return false, true
	}
	if length > maximumConstructedIntegerSequenceLength {
		return true, true
	}
	return addIntegerSequenceMaximumLength(requirements, int(length)), true
}

func collectAffineIntegerSequenceLengthEquality(
	value Equal,
	model integerSequenceModel,
	requirements *integerSequenceRequirementSet,
	aliases *integerSequenceAliases,
) (bool, bool, bool) {
	left, leftOK := value.Left.(Term[IntSort])
	right, rightOK := value.Right.(Term[IntSort])
	if !leftOK || !rightOK ||
		(!containsIntegerSequenceAffineLength(left) &&
			!containsIntegerSequenceAffineLength(right)) {
		return true, true, false
	}
	form := normalizeIntegerSequenceLengthAffine(left, right)
	if !form.valid {
		multi := normalizeIntegerSequenceLengthMultiAffine(left, right, aliases)
		if multi.valid {
			switch multi.count {
			case 0:
				return CompareIntegerValue(multi.constant, IntegerValue{}) == 0,
					true, true
			case 1:
				id := multi.ids[0]
				if _, assigned := model.lookup(id); assigned {
					result, ok := evaluateBoolWithIntegerSequences(
						value,
						booleanModel{},
						integerModel{},
						rationalModel{},
						model,
					)
					return result, ok, true
				}
				quotient, remainder, ok := DivModIntegerValue(
					NegateIntegerValue(multi.constant),
					multi.coefficients[0],
				)
				if !ok || CompareIntegerValue(remainder, IntegerValue{}) != 0 {
					return false, true, true
				}
				length, fits := quotient.Int64()
				if !fits || length > maximumConstructedIntegerSequenceLength {
					return true, false, true
				}
				if length < 0 {
					return false, true, true
				}
				return addIntegerSequenceExactLength(
					requirements.forSymbol(id), int(length),
				), true, true
			default:
				divisor := greatestCommonIntegerSequenceLengthCoefficient(multi)
				_, remainder, _ := DivModIntegerValue(
					NegateIntegerValue(multi.constant), divisor,
				)
				if CompareIntegerValue(remainder, IntegerValue{}) != 0 {
					return false, true, true
				}
				for index := 0; index < multi.count; index++ {
					requirements.forSymbol(multi.ids[index])
				}
				requirements.addRelation(integerSequenceLengthRelation{
					ids:          multi.ids,
					coefficients: multi.coefficients,
					count:        multi.count,
					constant:     multi.constant,
					equality:     true,
				})
				return true, true, true
			}
		}
		return true, false, true
	}
	if !form.hasSymbol {
		result, ok := evaluateBoolWithIntegerSequences(
			value, booleanModel{}, integerModel{}, rationalModel{}, model,
		)
		return result, ok, true
	}
	form.id = aliases.root(form.id)
	if _, assigned := model.lookup(form.id); assigned {
		result, ok := evaluateBoolWithIntegerSequences(
			value, booleanModel{}, integerModel{}, rationalModel{}, model,
		)
		return result, ok, true
	}
	if CompareIntegerValue(form.coefficient, IntegerValue{}) == 0 {
		consistent := CompareIntegerValue(form.constant, IntegerValue{}) == 0
		if consistent {
			requirements.forSymbol(form.id)
		}
		return consistent, true, true
	}
	quotient, remainder, ok := DivModIntegerValue(
		NegateIntegerValue(form.constant), form.coefficient,
	)
	if !ok || CompareIntegerValue(remainder, IntegerValue{}) != 0 {
		return false, true, true
	}
	length, fits := quotient.Int64()
	if !fits || length > maximumConstructedIntegerSequenceLength {
		return true, false, true
	}
	if length < 0 {
		return false, true, true
	}
	return addIntegerSequenceExactLength(
		requirements.forSymbol(form.id), int(length),
	), true, true
}

func collectAffineIntegerSequenceLengthBound(
	left,
	right Term[IntSort],
	strict bool,
	model integerSequenceModel,
	requirements *integerSequenceRequirementSet,
	aliases *integerSequenceAliases,
) (bool, bool, bool) {
	if !containsIntegerSequenceAffineLength(left) &&
		!containsIntegerSequenceAffineLength(right) {
		return true, true, false
	}
	form := normalizeIntegerSequenceLengthAffine(left, right)
	if !form.valid {
		multi := normalizeIntegerSequenceLengthMultiAffine(left, right, aliases)
		if !multi.valid {
			return true, false, true
		}
		if strict {
			multi.constant = AddIntegerValue(
				multi.constant, NewIntegerValue(1),
			)
		}
		switch multi.count {
		case 0:
			return CompareIntegerValue(multi.constant, IntegerValue{}) <= 0,
				true, true
		case 1:
			form = integerSequenceLengthAffine{
				id:          multi.ids[0],
				coefficient: multi.coefficients[0],
				constant:    multi.constant,
				hasSymbol:   true,
				valid:       true,
			}
			strict = false
		default:
			for index := 0; index < multi.count; index++ {
				requirements.forSymbol(multi.ids[index])
			}
			requirements.addRelation(integerSequenceLengthRelation{
				ids:          multi.ids,
				coefficients: multi.coefficients,
				count:        multi.count,
				constant:     multi.constant,
			})
			return true, true, true
		}
	}
	if !form.hasSymbol {
		var term Term[BoolSort] = LessEqual{Left: left, Right: right}
		if strict {
			term = Less{Left: left, Right: right}
		}
		result, ok := evaluateBoolWithIntegerSequences(
			term, booleanModel{}, integerModel{}, rationalModel{}, model,
		)
		return result, ok, true
	}
	form.id = aliases.root(form.id)
	if _, assigned := model.lookup(form.id); assigned {
		var term Term[BoolSort] = LessEqual{Left: left, Right: right}
		if strict {
			term = Less{Left: left, Right: right}
		}
		result, ok := evaluateBoolWithIntegerSequences(
			term, booleanModel{}, integerModel{}, rationalModel{}, model,
		)
		return result, ok, true
	}
	coefficientSign := CompareIntegerValue(form.coefficient, IntegerValue{})
	bound := NegateIntegerValue(form.constant)
	if strict {
		bound = AddIntegerValue(bound, NewIntegerValue(-1))
	}
	if coefficientSign == 0 {
		consistent := CompareIntegerValue(IntegerValue{}, bound) <= 0
		if consistent {
			requirements.forSymbol(form.id)
		}
		return consistent, true, true
	}
	quotient, _, ok := DivModIntegerValue(bound, form.coefficient)
	if !ok {
		return true, false, true
	}
	target := requirements.forSymbol(form.id)
	if coefficientSign > 0 {
		consistent, supported := applyIntegerSequenceMaximumValue(target, quotient)
		return consistent, supported, true
	}
	consistent, supported := applyIntegerSequenceMinimumValue(target, quotient)
	return consistent, supported, true
}

func collectPositiveIntegerSequenceRequirements(
	term Term[BoolSort],
	model integerSequenceModel,
	requirements *integerSequenceRequirementSet,
	aliases *integerSequenceAliases,
) (bool, bool) {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			consistent, supported := collectPositiveIntegerSequenceRequirements(
				item, model, requirements, aliases,
			)
			if !consistent || !supported {
				return consistent, supported
			}
		}
		return true, true
	case BooleanConjunction:
		items, negated := value.values()
		for index, item := range items {
			if negated[index] && containsIntegerSequenceTheory(item) {
				_, ok := evaluateBoolWithIntegerSequences(
					item, booleanModel{}, integerModel{}, rationalModel{}, model,
				)
				if !ok {
					return true, false
				}
			}
			if negated[index] {
				continue
			}
			consistent, supported := collectPositiveIntegerSequenceRequirements(
				item, model, requirements, aliases,
			)
			if !consistent || !supported {
				return consistent, supported
			}
		}
		return true, true
	case Equal:
		consistent, supported, recognized := collectAffineIntegerSequenceLengthEquality(
			value, model, requirements, aliases,
		)
		if recognized {
			return consistent, supported
		}
		lengthID, leftLength := symbolicIntegerSequenceLength(value.Left)
		lengthTerm := value.Right
		if !leftLength {
			lengthID, leftLength = symbolicIntegerSequenceLength(value.Right)
			lengthTerm = value.Left
		}
		if leftLength {
			lengthID = aliases.root(lengthID)
			if assigned, ok := model.lookup(lengthID); ok {
				ground, ok := lengthTerm.(Term[IntSort])
				if !ok {
					return true, false
				}
				expected, ok := evaluateInteger(
					ground, booleanModel{}, integerModel{}, rationalModel{},
				)
				if !ok {
					return true, false
				}
				actual, fits := expected.Int64()
				return fits && actual == int64(assigned.Len()), true
			}
			ground, ok := lengthTerm.(Term[IntSort])
			if !ok {
				return true, false
			}
			expected, ok := evaluateInteger(
				ground, booleanModel{}, integerModel{}, rationalModel{},
			)
			if !ok {
				return true, false
			}
			length, fits := expected.Int64()
			if !fits || length > maximumConstructedIntegerSequenceLength {
				return true, false
			}
			if length < 0 {
				return false, true
			}
			return addIntegerSequenceExactLength(
				requirements.forSymbol(lengthID), int(length),
			), true
		}
		leftID, leftSymbol := integerSequenceSymbolID(value.Left)
		_, rightSymbol := integerSequenceSymbolID(value.Right)
		if leftSymbol && rightSymbol {
			root := aliases.root(leftID)
			if _, assigned := model.lookup(root); !assigned {
				requirements.forSymbol(root)
			}
			return true, true
		}
		if leftSymbol || rightSymbol {
			return true, true
		}
		if containsIntegerSequenceTheory(term) {
			_, ok := evaluateBoolWithIntegerSequences(
				term, booleanModel{}, integerModel{}, rationalModel{}, model,
			)
			return true, ok
		}
		return true, true
	case Less:
		left, leftOK := value.Left.(Term[IntSort])
		right, rightOK := value.Right.(Term[IntSort])
		consistent, supported, recognized := true, true, false
		if leftOK && rightOK {
			consistent, supported, recognized = collectAffineIntegerSequenceLengthBound(
				left, right, true, model, requirements, aliases,
			)
		}
		if recognized {
			return consistent, supported
		}
		if containsIntegerSequenceTheory(term) {
			_, ok := evaluateBoolWithIntegerSequences(
				term, booleanModel{}, integerModel{}, rationalModel{}, model,
			)
			return true, ok
		}
		return true, true
	case LessEqual:
		left, leftOK := value.Left.(Term[IntSort])
		right, rightOK := value.Right.(Term[IntSort])
		consistent, supported, recognized := true, true, false
		if leftOK && rightOK {
			consistent, supported, recognized = collectAffineIntegerSequenceLengthBound(
				left, right, false, model, requirements, aliases,
			)
		}
		if recognized {
			return consistent, supported
		}
		if containsIntegerSequenceTheory(term) {
			_, ok := evaluateBoolWithIntegerSequences(
				term, booleanModel{}, integerModel{}, rationalModel{}, model,
			)
			return true, ok
		}
		return true, true
	case sequenceContains:
		sequence, sequenceOK := value.value.(Term[SequenceSort[IntSort]])
		part, partOK := value.subsequence.(Term[SequenceSort[IntSort]])
		if !sequenceOK || !partOK {
			return true, false
		}
		id, symbolic := integerSequenceSymbolID(sequence)
		id = aliases.root(id)
		if !symbolic {
			_, ok := evaluateBoolWithIntegerSequences(
				term, booleanModel{}, integerModel{}, rationalModel{}, model,
			)
			return true, ok
		}
		if _, assigned := model.lookup(id); assigned {
			return true, true
		}
		ground, ok := evaluateIntegerSequenceWithModel(
			part, booleanModel{}, integerModel{}, rationalModel{}, model,
		)
		if !ok {
			return true, false
		}
		requirements.forSymbol(id).addContainment(ground)
		return true, true
	case sequencePrefix:
		sequence, sequenceOK := value.value.(Term[SequenceSort[IntSort]])
		prefix, prefixOK := value.prefix.(Term[SequenceSort[IntSort]])
		if !sequenceOK || !prefixOK {
			return true, false
		}
		id, symbolic := integerSequenceSymbolID(sequence)
		id = aliases.root(id)
		if !symbolic {
			_, ok := evaluateBoolWithIntegerSequences(
				term, booleanModel{}, integerModel{}, rationalModel{}, model,
			)
			return true, ok
		}
		if _, assigned := model.lookup(id); assigned {
			return true, true
		}
		ground, ok := evaluateIntegerSequenceWithModel(
			prefix, booleanModel{}, integerModel{}, rationalModel{}, model,
		)
		if !ok {
			return true, false
		}
		return addIntegerSequencePrefix(requirements.forSymbol(id), ground), true
	case sequenceSuffix:
		sequence, sequenceOK := value.value.(Term[SequenceSort[IntSort]])
		suffix, suffixOK := value.suffix.(Term[SequenceSort[IntSort]])
		if !sequenceOK || !suffixOK {
			return true, false
		}
		id, symbolic := integerSequenceSymbolID(sequence)
		id = aliases.root(id)
		if !symbolic {
			_, ok := evaluateBoolWithIntegerSequences(
				term, booleanModel{}, integerModel{}, rationalModel{}, model,
			)
			return true, ok
		}
		if _, assigned := model.lookup(id); assigned {
			return true, true
		}
		ground, ok := evaluateIntegerSequenceWithModel(
			suffix, booleanModel{}, integerModel{}, rationalModel{}, model,
		)
		if !ok {
			return true, false
		}
		return addIntegerSequenceSuffix(requirements.forSymbol(id), ground), true
	default:
		if containsIntegerSequenceTheory(term) {
			_, ok := evaluateBoolWithIntegerSequences(
				term, booleanModel{}, integerModel{}, rationalModel{}, model,
			)
			return true, ok
		}
		return true, true
	}
}

type fixedIntegerSequenceBuilder struct {
	length         int
	inline         [8]IntegerValue
	inlineAssigned [8]bool
	overflow       []IntegerValue
	assigned       []bool
}

func newFixedIntegerSequenceBuilder(length int) fixedIntegerSequenceBuilder {
	result := fixedIntegerSequenceBuilder{length: length}
	if length > len(result.inline) {
		result.overflow = make([]IntegerValue, length)
		result.assigned = make([]bool, length)
	}
	return result
}

func (builder *fixedIntegerSequenceBuilder) valueAt(index int) (IntegerValue, bool) {
	if builder.overflow != nil {
		return builder.overflow[index], builder.assigned[index]
	}
	return builder.inline[index], builder.inlineAssigned[index]
}

func (builder *fixedIntegerSequenceBuilder) assign(index int, value IntegerValue) bool {
	existing, assigned := builder.valueAt(index)
	if assigned {
		return CompareIntegerValue(existing, value) == 0
	}
	if builder.overflow != nil {
		builder.overflow[index] = value
		builder.assigned[index] = true
	} else {
		builder.inline[index] = value
		builder.inlineAssigned[index] = true
	}
	return true
}

func (builder *fixedIntegerSequenceBuilder) clear(index int) {
	if builder.overflow != nil {
		builder.assigned[index] = false
		builder.overflow[index] = IntegerValue{}
	} else {
		builder.inlineAssigned[index] = false
		builder.inline[index] = IntegerValue{}
	}
}

func (builder *fixedIntegerSequenceBuilder) placeFixed(
	value IntegerSequenceValue,
	offset int,
) bool {
	for index := 0; index < value.Len(); index++ {
		element, _ := value.At(index)
		if !builder.assign(offset+index, element) {
			return false
		}
	}
	return true
}

func (builder *fixedIntegerSequenceBuilder) tryPlacement(
	value IntegerSequenceValue,
	offset int,
	changed *[8]int,
	overflow *[]int,
) bool {
	for index := 0; index < value.Len(); index++ {
		position := offset + index
		element, _ := value.At(index)
		existing, assigned := builder.valueAt(position)
		if assigned {
			if CompareIntegerValue(existing, element) != 0 {
				builder.rollbackPlacement(changed, overflow)
				return false
			}
			continue
		}
		builder.assign(position, element)
		if len(*overflow) != 0 || index >= len(changed) {
			*overflow = append(*overflow, position)
		} else {
			changed[index] = position + 1
		}
	}
	return true
}

func (builder *fixedIntegerSequenceBuilder) rollbackPlacement(
	changed *[8]int,
	overflow *[]int,
) {
	for index := range changed {
		if changed[index] != 0 {
			builder.clear(changed[index] - 1)
			changed[index] = 0
		}
	}
	for _, position := range *overflow {
		builder.clear(position)
	}
	*overflow = (*overflow)[:0]
}

func placeIntegerSequenceContainments(
	builder *fixedIntegerSequenceBuilder,
	requirements integerSequenceRequirements,
	index int,
	states *int,
) (bool, bool) {
	if index == requirements.containment {
		return true, true
	}
	part := requirements.containmentAt(index)
	for offset := 0; offset+part.Len() <= builder.length; offset++ {
		*states++
		if *states > maximumConstructedIntegerSequenceLength {
			return false, false
		}
		var changed [8]int
		var overflow []int
		if !builder.tryPlacement(part, offset, &changed, &overflow) {
			continue
		}
		found, complete := placeIntegerSequenceContainments(
			builder, requirements, index+1, states,
		)
		if found || !complete {
			return found, complete
		}
		builder.rollbackPlacement(&changed, &overflow)
	}
	return false, true
}

func buildFixedLengthIntegerSequenceWitness(
	requirements integerSequenceRequirements,
	states *int,
) (IntegerSequenceValue, bool, bool) {
	length := requirements.exactLength
	if requirements.prefix.Len() > length || requirements.suffix.Len() > length {
		return IntegerSequenceValue{}, false, true
	}
	for index := 0; index < requirements.containment; index++ {
		if requirements.containmentAt(index).Len() > length {
			return IntegerSequenceValue{}, false, true
		}
	}
	builder := newFixedIntegerSequenceBuilder(length)
	if requirements.hasPrefix && !builder.placeFixed(requirements.prefix, 0) {
		return IntegerSequenceValue{}, false, true
	}
	if requirements.hasSuffix &&
		!builder.placeFixed(requirements.suffix, length-requirements.suffix.Len()) {
		return IntegerSequenceValue{}, false, true
	}
	found, complete := placeIntegerSequenceContainments(
		&builder, requirements, 0, states,
	)
	if !found {
		return IntegerSequenceValue{}, !complete, complete
	}
	var result IntegerSequenceValue
	for index := 0; index < length; index++ {
		value, assigned := builder.valueAt(index)
		if !assigned {
			value = IntegerValue{}
		}
		result.append(value)
	}
	return result, true, true
}

func buildIntegerSequenceWitness(
	requirements integerSequenceRequirements,
) (IntegerSequenceValue, bool, bool) {
	if requirements.hasLength {
		states := 0
		return buildFixedLengthIntegerSequenceWitness(requirements, &states)
	}
	var result IntegerSequenceValue
	if requirements.hasPrefix {
		result.appendSequence(requirements.prefix)
	}
	for index := 0; index < requirements.containment; index++ {
		part := requirements.containmentAt(index)
		if findIntegerSubsequence(result, part, 0) < 0 {
			result.appendSequence(part)
		}
	}
	if requirements.hasSuffix && !integerSequenceEndsWith(result, requirements.suffix) {
		result.appendSequence(requirements.suffix)
	}
	if requirements.hasMax {
		minimum := 0
		if requirements.hasMin {
			minimum = requirements.minLength
		}
		for index := 0; index < requirements.containment; index++ {
			if length := requirements.containmentAt(index).Len(); length > minimum {
				minimum = length
			}
		}
		if requirements.prefix.Len() > minimum {
			minimum = requirements.prefix.Len()
		}
		if requirements.suffix.Len() > minimum {
			minimum = requirements.suffix.Len()
		}
		states := 0
		for length := minimum; length <= requirements.maxLength; length++ {
			candidate := requirements
			candidate.exactLength = length
			candidate.hasLength = true
			witness, consistent, supported := buildFixedLengthIntegerSequenceWitness(
				candidate, &states,
			)
			if !supported {
				return IntegerSequenceValue{}, true, false
			}
			if consistent {
				return witness, true, true
			}
		}
		return IntegerSequenceValue{}, false, true
	}
	if requirements.hasMin && result.Len() < requirements.minLength {
		candidate := requirements
		candidate.exactLength = requirements.minLength
		if result.Len() > candidate.exactLength {
			candidate.exactLength = result.Len()
		}
		candidate.hasLength = true
		states := 0
		return buildFixedLengthIntegerSequenceWitness(candidate, &states)
	}
	return result, true, true
}

func buildIntegerSequenceAtLength(
	requirements integerSequenceRequirements,
	length int,
) (IntegerSequenceValue, bool, bool) {
	if !addIntegerSequenceExactLength(&requirements, length) {
		return IntegerSequenceValue{}, false, true
	}
	return buildIntegerSequenceWitness(requirements)
}

type integerSequenceLengthSearch struct {
	relation     integerSequenceLengthRelation
	requirements [8]integerSequenceRequirements
	assigned     [8]IntegerSequenceValue
	hasAssigned  [8]bool
	values       [8]IntegerSequenceValue
	lengths      [8]int
	states       int
}

func integerSequenceLengthRange(
	requirements integerSequenceRequirements,
	assigned IntegerSequenceValue,
	hasAssigned bool,
) (int, int, bool) {
	if hasAssigned {
		length := assigned.Len()
		if requirements.hasMin && length < requirements.minLength ||
			requirements.hasMax && length > requirements.maxLength ||
			requirements.hasLength && length != requirements.exactLength {
			return 0, 0, false
		}
		return length, length, true
	}
	start, end := 0, maximumConstructedIntegerSequenceLength
	if requirements.hasPrefix && requirements.prefix.Len() > start {
		start = requirements.prefix.Len()
	}
	if requirements.hasSuffix && requirements.suffix.Len() > start {
		start = requirements.suffix.Len()
	}
	for index := 0; index < requirements.containment; index++ {
		if length := requirements.containmentAt(index).Len(); length > start {
			start = length
		}
	}
	if requirements.hasMin {
		if requirements.minLength > start {
			start = requirements.minLength
		}
	}
	if requirements.hasMax {
		end = requirements.maxLength
	}
	if requirements.hasLength {
		start, end = requirements.exactLength, requirements.exactLength
	}
	return start, end, start <= end
}

func (search *integerSequenceLengthSearch) buildCandidate() (bool, bool) {
	for index := 0; index < search.relation.count; index++ {
		if search.hasAssigned[index] {
			search.values[index] = search.assigned[index]
			continue
		}
		value, consistent, supported := buildIntegerSequenceAtLength(
			search.requirements[index], search.lengths[index],
		)
		if !supported {
			return false, false
		}
		if !consistent {
			return false, true
		}
		search.values[index] = value
	}
	return true, true
}

func (search *integerSequenceLengthSearch) inequalityCanStillHold(
	index int,
	sum IntegerValue,
) bool {
	for ; index < search.relation.count; index++ {
		start, end, admissible := integerSequenceLengthRange(
			search.requirements[index],
			search.assigned[index],
			search.hasAssigned[index],
		)
		if !admissible {
			return false
		}
		length := start
		if CompareIntegerValue(
			search.relation.coefficients[index], IntegerValue{},
		) < 0 {
			length = end
		}
		sum = AddIntegerValue(
			sum,
			MultiplyIntegerValue(
				search.relation.coefficients[index],
				NewIntegerValue(int64(length)),
			),
		)
	}
	return CompareIntegerValue(
		AddIntegerValue(sum, search.relation.constant),
		IntegerValue{},
	) <= 0
}

func (search *integerSequenceLengthSearch) solve(
	index int,
	sum IntegerValue,
) (bool, bool) {
	if index == search.relation.count-1 {
		search.states++
		if search.states > maximumConstructedIntegerSequenceLength {
			return false, false
		}
		right := NegateIntegerValue(AddIntegerValue(sum, search.relation.constant))
		start, end, admissible := integerSequenceLengthRange(
			search.requirements[index],
			search.assigned[index],
			search.hasAssigned[index],
		)
		if !admissible {
			return false, true
		}
		lengthValue, remainder, ok := DivModIntegerValue(
			right, search.relation.coefficients[index],
		)
		if !ok {
			return false, true
		}
		if search.relation.equality {
			if CompareIntegerValue(remainder, IntegerValue{}) != 0 {
				return false, true
			}
			length, fits := lengthValue.Int64()
			if !fits || length < int64(start) || length > int64(end) {
				return false, true
			}
			search.lengths[index] = int(length)
			return search.buildCandidate()
		}
		length, fits := lengthValue.Int64()
		coefficientSign := CompareIntegerValue(
			search.relation.coefficients[index], IntegerValue{},
		)
		if coefficientSign > 0 {
			if fits && int64(end) > length {
				end = int(length)
			} else if !fits && CompareIntegerValue(lengthValue, IntegerValue{}) < 0 {
				return false, true
			}
		} else {
			if fits && int64(start) < length {
				start = int(length)
			} else if !fits && CompareIntegerValue(lengthValue, IntegerValue{}) > 0 {
				return false, true
			}
		}
		if start > end {
			return false, true
		}
		search.lengths[index] = start
		return search.buildCandidate()
	}
	start, end, admissible := integerSequenceLengthRange(
		search.requirements[index],
		search.assigned[index],
		search.hasAssigned[index],
	)
	if !admissible {
		return false, true
	}
	for length := start; length <= end; length++ {
		search.lengths[index] = length
		term := MultiplyIntegerValue(
			search.relation.coefficients[index],
			NewIntegerValue(int64(length)),
		)
		nextSum := AddIntegerValue(sum, term)
		if !search.relation.equality &&
			!search.inequalityCanStillHold(index+1, nextSum) {
			continue
		}
		found, complete := search.solve(index+1, nextSum)
		if found || !complete {
			return found, complete
		}
	}
	return false, true
}

func solveIntegerSequenceLengthRelation(
	relation integerSequenceLengthRelation,
	requirements *integerSequenceRequirementSet,
	model *integerSequenceModel,
) (bool, bool) {
	search := integerSequenceLengthSearch{relation: relation}
	for index := 0; index < relation.count; index++ {
		search.requirements[index] = *requirements.forSymbol(relation.ids[index])
		search.assigned[index], search.hasAssigned[index] =
			model.lookup(relation.ids[index])
	}
	found, complete := search.solve(0, IntegerValue{})
	if !complete {
		return true, false
	}
	if !found {
		return false, true
	}
	for index := 0; index < relation.count; index++ {
		if !model.set(relation.ids[index], search.values[index]) {
			return false, true
		}
	}
	return true, true
}

type integerSequenceLengthSystemSearch struct {
	relations    *integerSequenceRequirementSet
	ids          [8]int
	count        int
	requirements [8]integerSequenceRequirements
	assigned     [8]IntegerSequenceValue
	hasAssigned  [8]bool
	values       [8]IntegerSequenceValue
	lengths      [8]int
	states       int
}

func (search *integerSequenceLengthSystemSearch) addID(id int) bool {
	for index := 0; index < search.count; index++ {
		if search.ids[index] == id {
			return true
		}
	}
	if search.count == len(search.ids) {
		return false
	}
	search.ids[search.count] = id
	search.count++
	return true
}

func integerSequenceLengthRelationCoefficient(
	relation integerSequenceLengthRelation,
	id int,
) IntegerValue {
	for index := 0; index < relation.count; index++ {
		if relation.ids[index] == id {
			return relation.coefficients[index]
		}
	}
	return IntegerValue{}
}

func (search *integerSequenceLengthSystemSearch) relationBounds(
	relation integerSequenceLengthRelation,
	known int,
) (IntegerValue, IntegerValue, bool) {
	minimum, maximum := relation.constant, relation.constant
	for index := 0; index < search.count; index++ {
		coefficient := integerSequenceLengthRelationCoefficient(
			relation, search.ids[index],
		)
		if CompareIntegerValue(coefficient, IntegerValue{}) == 0 {
			continue
		}
		start, end := search.lengths[index], search.lengths[index]
		if index >= known {
			var admissible bool
			start, end, admissible = integerSequenceLengthRange(
				search.requirements[index],
				search.assigned[index],
				search.hasAssigned[index],
			)
			if !admissible {
				return IntegerValue{}, IntegerValue{}, false
			}
		}
		minimumLength, maximumLength := start, end
		if CompareIntegerValue(coefficient, IntegerValue{}) < 0 {
			minimumLength, maximumLength = end, start
		}
		minimum = AddIntegerValue(
			minimum,
			MultiplyIntegerValue(
				coefficient, NewIntegerValue(int64(minimumLength)),
			),
		)
		maximum = AddIntegerValue(
			maximum,
			MultiplyIntegerValue(
				coefficient, NewIntegerValue(int64(maximumLength)),
			),
		)
	}
	return minimum, maximum, true
}

func (search *integerSequenceLengthSystemSearch) canStillHold(known int) bool {
	for index := 0; index < search.relations.relationCount; index++ {
		relation := search.relations.relationAt(index)
		minimum, maximum, admissible := search.relationBounds(relation, known)
		if !admissible {
			return false
		}
		if relation.equality {
			if CompareIntegerValue(minimum, IntegerValue{}) > 0 ||
				CompareIntegerValue(maximum, IntegerValue{}) < 0 {
				return false
			}
		} else if CompareIntegerValue(minimum, IntegerValue{}) > 0 {
			return false
		}
	}
	return true
}

func (search *integerSequenceLengthSystemSearch) buildCandidate() (bool, bool) {
	for index := 0; index < search.count; index++ {
		if search.hasAssigned[index] {
			search.values[index] = search.assigned[index]
			continue
		}
		value, consistent, supported := buildIntegerSequenceAtLength(
			search.requirements[index], search.lengths[index],
		)
		if !supported {
			return false, false
		}
		if !consistent {
			return false, true
		}
		search.values[index] = value
	}
	return true, true
}

func (search *integerSequenceLengthSystemSearch) solveFinal(
	index int,
) (bool, bool) {
	search.states++
	if search.states > maximumConstructedIntegerSequenceLength {
		return false, false
	}
	start, end, admissible := integerSequenceLengthRange(
		search.requirements[index],
		search.assigned[index],
		search.hasAssigned[index],
	)
	if !admissible {
		return false, true
	}
	for relationIndex := 0; relationIndex < search.relations.relationCount; relationIndex++ {
		relation := search.relations.relationAt(relationIndex)
		sum := relation.constant
		for known := 0; known < index; known++ {
			sum = AddIntegerValue(
				sum,
				MultiplyIntegerValue(
					integerSequenceLengthRelationCoefficient(
						relation, search.ids[known],
					),
					NewIntegerValue(int64(search.lengths[known])),
				),
			)
		}
		coefficient := integerSequenceLengthRelationCoefficient(
			relation, search.ids[index],
		)
		coefficientSign := CompareIntegerValue(coefficient, IntegerValue{})
		if coefficientSign == 0 {
			comparison := CompareIntegerValue(sum, IntegerValue{})
			if relation.equality && comparison != 0 ||
				!relation.equality && comparison > 0 {
				return false, true
			}
			continue
		}
		quotient, remainder, _ := DivModIntegerValue(
			NegateIntegerValue(sum), coefficient,
		)
		if relation.equality {
			if CompareIntegerValue(remainder, IntegerValue{}) != 0 {
				return false, true
			}
			length, fits := quotient.Int64()
			if !fits || length < int64(start) || length > int64(end) {
				return false, true
			}
			start, end = int(length), int(length)
			continue
		}
		length, fits := quotient.Int64()
		if coefficientSign > 0 {
			if fits && int64(end) > length {
				end = int(length)
			} else if !fits && CompareIntegerValue(quotient, IntegerValue{}) < 0 {
				return false, true
			}
		} else {
			if fits && int64(start) < length {
				start = int(length)
			} else if !fits && CompareIntegerValue(quotient, IntegerValue{}) > 0 {
				return false, true
			}
		}
		if start > end {
			return false, true
		}
	}
	search.lengths[index] = start
	return search.buildCandidate()
}

func (search *integerSequenceLengthSystemSearch) solve(
	index int,
) (bool, bool) {
	if index == search.count-1 {
		return search.solveFinal(index)
	}
	start, end, admissible := integerSequenceLengthRange(
		search.requirements[index],
		search.assigned[index],
		search.hasAssigned[index],
	)
	if !admissible {
		return false, true
	}
	for length := start; length <= end; length++ {
		search.lengths[index] = length
		if !search.canStillHold(index + 1) {
			continue
		}
		found, complete := search.solve(index + 1)
		if found || !complete {
			return found, complete
		}
	}
	return false, true
}

func solveIntegerSequenceLengthSystem(
	requirements *integerSequenceRequirementSet,
	model *integerSequenceModel,
) (bool, bool) {
	search := integerSequenceLengthSystemSearch{relations: requirements}
	for relationIndex := 0; relationIndex < requirements.relationCount; relationIndex++ {
		relation := requirements.relationAt(relationIndex)
		for index := 0; index < relation.count; index++ {
			if !search.addID(relation.ids[index]) {
				return true, false
			}
		}
	}
	for index := 0; index < search.count; index++ {
		search.requirements[index] = *requirements.forSymbol(search.ids[index])
		search.assigned[index], search.hasAssigned[index] =
			model.lookup(search.ids[index])
	}
	found, complete := search.solve(0)
	if !complete {
		return true, false
	}
	if !found {
		return false, true
	}
	for index := 0; index < search.count; index++ {
		if !model.set(search.ids[index], search.values[index]) {
			return false, true
		}
	}
	return true, true
}

func bindPositiveIntegerSequenceWitnesses(
	assertions []Term[BoolSort],
	model *integerSequenceModel,
	aliases *integerSequenceAliases,
) (bool, bool) {
	var requirements integerSequenceRequirementSet
	for _, assertion := range assertions {
		consistent, supported := collectPositiveIntegerSequenceRequirements(
			assertion, *model, &requirements, aliases,
		)
		if !consistent || !supported {
			return consistent, supported
		}
	}
	if requirements.relationCount == 1 {
		consistent, supported := solveIntegerSequenceLengthRelation(
			requirements.relationAt(0), &requirements, model,
		)
		if !consistent || !supported {
			return consistent, supported
		}
	} else if requirements.relationCount > 1 {
		consistent, supported := solveIntegerSequenceLengthSystem(
			&requirements, model,
		)
		if !consistent || !supported {
			return consistent, supported
		}
	}
	for index := 0; index < requirements.count && index < len(requirements.inline); index++ {
		entry := requirements.inline[index]
		if _, assigned := model.lookup(entry.id); assigned {
			continue
		}
		witness, consistent, supported := buildIntegerSequenceWitness(entry.requirements)
		if !consistent || !supported {
			return consistent, supported
		}
		if !model.set(entry.id, witness) {
			return false, true
		}
	}
	for id, entry := range requirements.overflow {
		if _, assigned := model.lookup(id); assigned {
			continue
		}
		witness, consistent, supported := buildIntegerSequenceWitness(*entry)
		if !consistent || !supported {
			return consistent, supported
		}
		if !model.set(id, witness) {
			return false, true
		}
	}
	return true, true
}

func solveIntegerSequenceAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	found := false
	for _, assertion := range assertions {
		found = found || containsIntegerSequenceTheory(assertion)
	}
	if !found {
		return checkOutcome{}, false
	}
	var sequences integerSequenceModel
	var aliases integerSequenceAliases
	for _, assertion := range assertions {
		collectIntegerSequenceAliases(assertion, &aliases)
	}
	for _, assertion := range assertions {
		consistent, bound := bindGroundIntegerSequenceAssignments(
			assertion, &sequences, &aliases,
		)
		if bound && !consistent {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	if !expandIntegerSequenceAliases(&aliases, &sequences) {
		return checkOutcome{status: checkUnsat}, true
	}
	consistent, supported := bindPositiveIntegerSequenceWitnesses(
		assertions, &sequences, &aliases,
	)
	if !consistent {
		return checkOutcome{status: checkUnsat}, true
	}
	if !supported {
		return checkOutcome{
			status: checkUnknown,
			reason: UnsupportedTheory{Name: "integer sequence expression outside the positive symbolic fragment"},
		}, true
	}
	if !expandIntegerSequenceAliases(&aliases, &sequences) {
		return checkOutcome{status: checkUnsat}, true
	}
	for _, assertion := range assertions {
		value, ok := evaluateBoolWithIntegerSequences(
			assertion, booleanModel{}, integerModel{}, rationalModel{}, sequences,
		)
		if !ok {
			return checkOutcome{
				status: checkUnknown,
				reason: UnsupportedTheory{Name: "integer sequence expression outside the ground-assigned fragment"},
			}, true
		}
		if !value {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	return checkOutcome{status: checkSat, integerSequences: sequences}, true
}

func evaluateBoolWithStringsDatatypesAndSequences(
	term Term[BoolSort],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
	strings stringModel,
	sequences integerSequenceModel,
	datatypes *datatypeModel,
) (bool, bool) {
	if containsIntegerSequenceTheory(term) {
		return evaluateBoolWithIntegerSequences(term, booleans, integers, reals, sequences)
	}
	return evaluateBoolWithStringsAndDatatypes(
		term, booleans, integers, reals, strings, datatypes,
	)
}

func evaluateIntWithSequences(
	term Term[IntSort],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
	sequences integerSequenceModel,
) (int64, bool) {
	value, ok := evaluateIntegerWithSequences(
		term, booleans, integers, reals, bitVectorModel{}, sequences,
	)
	if !ok {
		return 0, false
	}
	return value.Int64()
}

func evaluateIntegerModelWithSequences(
	term Term[IntSort],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
	bitVectors bitVectorModel,
	sequences integerSequenceModel,
) (IntegerValue, bool) {
	return evaluateIntegerWithSequences(
		term, booleans, integers, reals, bitVectors, sequences,
	)
}

func evaluateIntegerModelTermWithSequences(
	term Term[IntSort],
	booleans booleanModel,
	integers integerModel,
	reals rationalModel,
	bitVectors bitVectorModel,
	sequences integerSequenceModel,
	arrays *integerArrayModel,
) (IntegerValue, bool) {
	if containsIntegerSequenceLength(term) {
		return evaluateIntegerWithSequences(
			term, booleans, integers, reals, bitVectors, sequences,
		)
	}
	return evaluateIntegerModelTerm(
		term, booleans, integers, reals, bitVectors, arrays,
	)
}

// IntegerSequenceModelValue evaluates an integer sequence in model.
func IntegerSequenceModelValue(
	model Model,
	term Term[SequenceSort[IntSort]],
) (IntegerSequenceValue, bool) {
	return evaluateIntegerSequenceWithModel(
		term, model.booleans, model.integers, model.reals, model.integerSequences,
	)
}
