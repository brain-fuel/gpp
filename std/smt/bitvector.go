package smt

import "math/big"

// BitVectorRelation is a compact unary equality or disequality retained by
// compatibility layers. If Masked is set it denotes symbol & Mask = Value.
type BitVectorRelation struct {
	Width      int
	SymbolID   int
	Value      BitVectorValue
	Mask       BitVectorValue
	Masked     bool
	Negated    bool
	Order      uint8
	Operation  uint8
	Operand    BitVectorValue
	ParameterA int
	ParameterB int
	Predicate  uint8
}

func (BitVectorRelation) isTerm(BoolSort) {}

type BitVectorConjunction struct {
	Count    int
	Inline   [4]BitVectorRelation
	Overflow []BitVectorRelation
}

func (BitVectorConjunction) isTerm(BoolSort) {}

// BitVectorIntegerRelation is the compact, allocation-free boundary between
// a bit-vector symbol conversion and an exact integer constant.
type BitVectorIntegerRelation struct {
	SymbolID  int
	Width     int
	Signed    bool
	Constant  IntegerValue
	Operation int8
	Reverse   bool
	Negated   bool
}

func (BitVectorIntegerRelation) isTerm(BoolSort) {}

type BitVectorMixedConjunction struct {
	BitVectorCount int
	BitVectors     [4]BitVectorRelation
	IntegerCount   int
	Integers       [4]BitVectorIntegerRelation
}

func (BitVectorMixedConjunction) isTerm(BoolSort) {}

// CompactBitVectorIntegerEquality recognizes the common symbol-conversion
// equality without exposing the internal indexed term representation.
func CompactBitVectorIntegerEquality(left, right Term[IntSort]) (BitVectorIntegerRelation, bool) {
	conversion, constant, reverse, ok := compactConversionOperands(left, right)
	if !ok {
		return BitVectorIntegerRelation{}, false
	}
	symbol, ok := conversion.value.(bitVectorSymbol[BitVecSort])
	if !ok {
		return BitVectorIntegerRelation{}, false
	}
	return BitVectorIntegerRelation{SymbolID: symbol.iD, Width: symbol.width, Signed: conversion.signed, Constant: constant, Reverse: reverse}, true
}

type BitVectorEUFTerm struct {
	Kind       uint8
	Width      int
	SymbolID   int
	FunctionID int
	FirstID    int
	FirstWidth int
}

type BitVectorEUFRelation struct {
	Left    BitVectorEUFTerm
	Right   BitVectorEUFTerm
	Negated bool
}

func (BitVectorEUFRelation) isTerm(BoolSort) {}

type BitVectorEUFConjunction struct {
	Count    int
	Inline   [4]BitVectorEUFRelation
	Overflow []BitVectorEUFRelation
}

func (BitVectorEUFConjunction) isTerm(BoolSort) {}

func (value BitVectorEUFConjunction) values() []BitVectorEUFRelation {
	if value.Overflow != nil {
		return value.Overflow[:value.Count]
	}
	return value.Inline[:value.Count]
}

func (value BitVectorConjunction) values() []BitVectorRelation {
	if value.Overflow != nil {
		return value.Overflow[:value.Count]
	}
	return value.Inline[:value.Count]
}

type bitVectorSymbolBit struct {
	id  int
	bit int
}

type bitVectorModelEntry struct {
	id    int
	value BitVectorValue
}
type bitVectorModel struct {
	count        int
	inline       [4]bitVectorModelEntry
	overflow     map[int]BitVectorValue
	applications []bitVectorApplicationModelEntry
}

type bitVectorApplicationModelEntry struct {
	functionID int
	arity      uint8
	first      BitVectorValue
	second     BitVectorValue
	value      BitVectorValue
}

func (model *bitVectorModel) set(id int, value BitVectorValue) {
	if model.count < len(model.inline) {
		model.inline[model.count] = bitVectorModelEntry{id: id, value: value}
		model.count++
		return
	}
	if model.overflow == nil {
		model.overflow = make(map[int]BitVectorValue)
	}
	model.overflow[id] = value
}

func (model bitVectorModel) lookup(id int) (BitVectorValue, bool) {
	for index := 0; index < model.count; index++ {
		if model.inline[index].id == id {
			return model.inline[index].value, true
		}
	}
	value, ok := model.overflow[id]
	return value, ok
}

func (model *bitVectorModel) merge(other bitVectorModel) {
	for index := 0; index < other.count; index++ {
		entry := other.inline[index]
		model.set(entry.id, entry.value)
	}
	for id, value := range other.overflow {
		model.set(id, value)
	}
	model.applications = append(model.applications, other.applications...)
}

func (model bitVectorModel) lookupApplication(functionID int, first BitVectorValue, second BitVectorValue, arity uint8) (BitVectorValue, bool) {
	for _, application := range model.applications {
		if application.functionID == functionID && application.arity == arity && EqualBitVectorValue(application.first, first) && (arity == 1 || EqualBitVectorValue(application.second, second)) {
			return application.value, true
		}
	}
	return BitVectorValue{}, false
}

type bitVectorEncodedApplication struct {
	functionID int
	arity      uint8
	first      []int
	second     []int
	result     []int
}

type bitVectorEncoder struct {
	cnf          booleanEncoder
	trueLit      int
	symbols      map[bitVectorSymbolBit]int
	widths       map[int]int
	applications []bitVectorEncodedApplication
}

func containsBitVectorTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			if containsBitVectorTheory(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsBitVectorTheory(item) {
				return true
			}
		}
	case Not:
		return containsBitVectorTheory(value.Value)
	case Or:
		for _, item := range value.Values {
			if containsBitVectorTheory(item) {
				return true
			}
		}
	case Implies:
		return containsBitVectorTheory(value.Left) || containsBitVectorTheory(value.Right)
	case Iff:
		return containsBitVectorTheory(value.Left) || containsBitVectorTheory(value.Right)
	case Equal:
		return isBitVectorTerm(value.Left) || isBitVectorTerm(value.Right) || containsBitVectorIntegerTerm(value.Left) || containsBitVectorIntegerTerm(value.Right)
	case LessEqual:
		return containsBitVectorIntegerTerm(value.Left) || containsBitVectorIntegerTerm(value.Right)
	case Less:
		return containsBitVectorIntegerTerm(value.Left) || containsBitVectorIntegerTerm(value.Right)
	case bitVectorUnsignedLess[BoolSort], bitVectorSignedLess[BoolSort]:
		return true
	case bitVectorUnsignedAddOverflow[BoolSort], bitVectorSignedAddOverflow[BoolSort], bitVectorUnsignedSubOverflow[BoolSort], bitVectorSignedSubOverflow[BoolSort], bitVectorUnsignedMulOverflow[BoolSort], bitVectorSignedMulOverflow[BoolSort], bitVectorSignedDivOverflow[BoolSort], bitVectorNegOverflow[BoolSort]:
		return true
	case BitVectorRelation, BitVectorConjunction, BitVectorIntegerRelation, BitVectorMixedConjunction, BitVectorEUFRelation, BitVectorEUFConjunction:
		return true
	}
	return false
}

func isBitVectorTerm(term any) bool {
	switch term.(type) {
	case bitVector[BitVecSort], bitVectorSymbol[BitVecSort], bitVectorNot[BitVecSort], bitVectorAnd[BitVecSort], bitVectorOr[BitVecSort], bitVectorXor[BitVecSort], bitVectorAdd[BitVecSort], bitVectorSub[BitVecSort], bitVectorMul[BitVecSort], bitVectorShiftLeft[BitVecSort], bitVectorLogicalShiftRight[BitVecSort], bitVectorArithmeticShiftRight[BitVecSort], bitVectorUnsignedDiv[BitVecSort], bitVectorUnsignedRem[BitVecSort], bitVectorSignedDiv[BitVecSort], bitVectorSignedRem[BitVecSort], bitVectorConcat[BitVecSort], bitVectorExtract[BitVecSort], bitVectorZeroExtend[BitVecSort], bitVectorSignExtend[BitVecSort], bitVectorRotateLeft[BitVecSort], bitVectorRotateRight[BitVecSort], bitVectorRepeat[BitVecSort], sortedUnaryApplication[BitVecSort], sortedBinaryApplication[BitVecSort], integerToBitVector[BitVecSort]:
		return true
	}
	return false
}

func containsBitVectorIntegerTerm(term any) bool {
	switch value := term.(type) {
	case bitVectorToInteger[IntSort]:
		return true
	case Add:
		for _, item := range value.Values {
			if containsBitVectorIntegerTerm(item) {
				return true
			}
		}
	case Subtract:
		return containsBitVectorIntegerTerm(value.Left) || containsBitVectorIntegerTerm(value.Right)
	case IntegerScale:
		return containsBitVectorIntegerTerm(value.Value)
	case IntegerDiv:
		return containsBitVectorIntegerTerm(value.Dividend)
	case IntegerMod:
		return containsBitVectorIntegerTerm(value.Dividend)
	case If[IntSort]:
		return containsBitVectorIntegerTerm(value.Then) || containsBitVectorIntegerTerm(value.Else)
	}
	return false
}

func solveBitVectorAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if outcome, recognized := solveCompactBitVectorAssertions(assertions); recognized {
		return outcome, true
	}
	if outcome, recognized := solveGroundBitVectorEUFContradiction(assertions); recognized {
		return outcome, true
	}
	encoder := bitVectorEncoder{symbols: make(map[bitVectorSymbolBit]int), widths: make(map[int]int)}
	encoder.cnf.initialize(len(assertions) * 32)
	encoder.trueLit = encoder.cnf.variable()
	encoder.cnf.addClause(encoder.trueLit)
	for _, assertion := range assertions {
		literal, ok := encoder.boolean(assertion)
		if !ok {
			return checkOutcome{}, false
		}
		encoder.cnf.addClause(literal)
	}
	assignment, sat := solveCNF(encoder.cnf.nextVariable, encoder.cnf.literals, encoder.cnf.clauses)
	if !sat {
		return checkOutcome{status: checkUnsat}, true
	}
	var model bitVectorModel
	for id, width := range encoder.widths {
		value := bitVectorValueFromBits(width, func(bit int) bool { return assignment.positive(encoder.symbols[bitVectorSymbolBit{id: id, bit: bit}]) })
		model.set(id, value)
	}
	for _, application := range encoder.applications {
		first := bitVectorValueFromBits(len(application.first), func(bit int) bool { return assignment.literalPositive(application.first[bit]) })
		second := BitVectorValue{}
		if application.arity == 2 {
			second = bitVectorValueFromBits(len(application.second), func(bit int) bool { return assignment.literalPositive(application.second[bit]) })
		}
		value := bitVectorValueFromBits(len(application.result), func(bit int) bool { return assignment.literalPositive(application.result[bit]) })
		model.applications = append(model.applications, bitVectorApplicationModelEntry{functionID: application.functionID, arity: application.arity, first: first, second: second, value: value})
	}
	return checkOutcome{status: checkSat, bitVectors: model}, true
}

func solveGroundBitVectorEUFContradiction(assertions []Term[BoolSort]) (checkOutcome, bool) {
	problem := eufProblem{}
	problem.initialize()
	for _, assertion := range assertions {
		if !problem.boolean(assertion, false) {
			return checkOutcome{}, false
		}
	}
	outcome, recognized := problem.solve()
	if recognized && outcome.status == checkUnsat {
		return outcome, true
	}
	return checkOutcome{}, false
}

type compactBitVectorAssignment struct {
	id    int
	value BitVectorValue
}

type compactBitVectorIntegerRelation struct {
	symbolID  int
	signed    bool
	constant  IntegerValue
	operation int
	reverse   bool
	negated   bool
}

type compactBitVectorProblem struct {
	relationCount   int
	relations       [8]BitVectorRelation
	conversionCount int
	conversions     [8]compactBitVectorIntegerRelation
}

func (problem *compactBitVectorProblem) add(term Term[BoolSort], negated bool) bool {
	switch value := term.(type) {
	case And:
		if negated {
			return false
		}
		for _, item := range value.Values {
			if !problem.add(item, false) {
				return false
			}
		}
		return true
	case BooleanConjunction:
		if negated {
			return false
		}
		items, itemNegated := value.values()
		for index, item := range items {
			if !problem.add(item, itemNegated[index]) {
				return false
			}
		}
		return true
	case Not:
		return problem.add(value.Value, !negated)
	case BitVectorRelation:
		if problem.relationCount == len(problem.relations) {
			return false
		}
		value.Negated = value.Negated != negated
		problem.relations[problem.relationCount] = value
		problem.relationCount++
		return true
	case BitVectorConjunction:
		if negated || problem.relationCount+value.Count > len(problem.relations) {
			return false
		}
		for _, relation := range value.values() {
			problem.relations[problem.relationCount] = relation
			problem.relationCount++
		}
		return true
	case BitVectorIntegerRelation:
		if problem.conversionCount == len(problem.conversions) {
			return false
		}
		problem.conversions[problem.conversionCount] = compactBitVectorIntegerRelation{symbolID: value.SymbolID, signed: value.Signed, constant: value.Constant, operation: int(value.Operation), reverse: value.Reverse, negated: value.Negated != negated}
		problem.conversionCount++
		return true
	case BitVectorMixedConjunction:
		if negated || value.BitVectorCount > len(value.BitVectors) || value.IntegerCount > len(value.Integers) {
			return false
		}
		if problem.relationCount+value.BitVectorCount > len(problem.relations) || problem.conversionCount+value.IntegerCount > len(problem.conversions) {
			return false
		}
		for index := 0; index < value.BitVectorCount; index++ {
			problem.relations[problem.relationCount] = value.BitVectors[index]
			problem.relationCount++
		}
		for index := 0; index < value.IntegerCount; index++ {
			item := value.Integers[index]
			problem.conversions[problem.conversionCount] = compactBitVectorIntegerRelation{symbolID: item.SymbolID, signed: item.Signed, constant: item.Constant, operation: int(item.Operation), reverse: item.Reverse, negated: item.Negated}
			problem.conversionCount++
		}
		return true
	case Equal:
		left, leftOK := value.Left.(Term[IntSort])
		right, rightOK := value.Right.(Term[IntSort])
		return leftOK && rightOK && problem.addConversion(left, right, 0, negated)
	case Less:
		return problem.addConversion(value.Left, value.Right, -1, negated)
	case LessEqual:
		return problem.addConversion(value.Left, value.Right, -2, negated)
	}
	return false
}

func (problem *compactBitVectorProblem) addConversion(left, right Term[IntSort], operation int, negated bool) bool {
	if problem.conversionCount == len(problem.conversions) {
		return false
	}
	conversion, constant, reverse, ok := compactConversionOperands(left, right)
	if !ok {
		return false
	}
	symbol, ok := conversion.value.(bitVectorSymbol[BitVecSort])
	if !ok {
		return false
	}
	problem.conversions[problem.conversionCount] = compactBitVectorIntegerRelation{symbolID: symbol.iD, signed: conversion.signed, constant: constant, operation: operation, reverse: reverse, negated: negated}
	problem.conversionCount++
	return true
}

func compactConversionOperands(left, right Term[IntSort]) (bitVectorToInteger[IntSort], IntegerValue, bool, bool) {
	if conversion, ok := left.(bitVectorToInteger[IntSort]); ok {
		constant, constantOK := exactIntegerConstant(right)
		return conversion, constant, false, constantOK
	}
	if conversion, ok := right.(bitVectorToInteger[IntSort]); ok {
		constant, constantOK := exactIntegerConstant(left)
		return conversion, constant, true, constantOK
	}
	return bitVectorToInteger[IntSort]{}, IntegerValue{}, false, false
}

func solveCompactBitVectorAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	var problem compactBitVectorProblem
	for _, assertion := range assertions {
		if !problem.add(assertion, false) {
			return checkOutcome{}, false
		}
	}
	relations := problem.relations[:problem.relationCount]
	var assignments [4]compactBitVectorAssignment
	assignmentCount := 0
	for _, relation := range relations {
		if relation.Masked || relation.Negated || relation.Order != 0 || relation.Operation != 0 || relation.Predicate != 0 {
			continue
		}
		found := false
		for index := 0; index < assignmentCount; index++ {
			if assignments[index].id != relation.SymbolID {
				continue
			}
			found = true
			if !EqualBitVectorValue(assignments[index].value, relation.Value) {
				return checkOutcome{status: checkUnsat}, true
			}
		}
		if !found {
			if assignmentCount == len(assignments) {
				return checkOutcome{}, false
			}
			assignments[assignmentCount] = compactBitVectorAssignment{id: relation.SymbolID, value: relation.Value}
			assignmentCount++
		}
	}
	for _, conversion := range problem.conversions[:problem.conversionCount] {
		var assigned BitVectorValue
		found := false
		for index := 0; index < assignmentCount; index++ {
			if assignments[index].id == conversion.symbolID {
				assigned, found = assignments[index].value, true
				break
			}
		}
		if !found {
			return checkOutcome{}, false
		}
		actual := BitVectorToIntegerValue(assigned, conversion.signed)
		comparison := CompareIntegerValue(actual, conversion.constant)
		if conversion.reverse {
			comparison = -comparison
		}
		holds := comparison == 0
		if conversion.operation == -1 {
			holds = comparison < 0
		}
		if conversion.operation == -2 {
			holds = comparison <= 0
		}
		if holds == conversion.negated {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	for _, relation := range relations {
		var assigned BitVectorValue
		found := false
		for index := 0; index < assignmentCount; index++ {
			if assignments[index].id == relation.SymbolID {
				assigned, found = assignments[index].value, true
				break
			}
		}
		if !found {
			return checkOutcome{}, false
		}
		actual := assigned
		switch relation.Operation {
		case 1:
			actual = AddBitVectorValue(actual, relation.Operand)
		case 2:
			actual = SubBitVectorValue(actual, relation.Operand)
		case 3:
			actual = MulBitVectorValue(actual, relation.Operand)
		case 4:
			actual = ShiftLeftBitVectorValue(actual, relation.Operand)
		case 5:
			actual = LogicalShiftRightBitVectorValue(actual, relation.Operand)
		case 6:
			actual = ArithmeticShiftRightBitVectorValue(actual, relation.Operand)
		case 7:
			actual = UnsignedDivBitVectorValue(actual, relation.Operand)
		case 8:
			actual = UnsignedRemBitVectorValue(actual, relation.Operand)
		case 9:
			actual = SignedDivBitVectorValue(actual, relation.Operand)
		case 10:
			actual = SignedRemBitVectorValue(actual, relation.Operand)
		case 11:
			actual = ExtractBitVectorValue(actual, relation.ParameterA, relation.ParameterB)
		case 12:
			actual = ZeroExtendBitVectorValue(actual, relation.ParameterA)
		case 13:
			actual = SignExtendBitVectorValue(actual, relation.ParameterA)
		case 14:
			actual = RotateLeftBitVectorValue(actual, relation.ParameterA)
		case 15:
			actual = RotateRightBitVectorValue(actual, relation.ParameterA)
		case 16:
			actual = RepeatBitVectorValue(actual, relation.ParameterA)
		}
		if relation.Masked {
			actual = AndBitVectorValue(actual, relation.Mask)
		}
		holds := EqualBitVectorValue(actual, relation.Value)
		switch relation.Predicate {
		case 1:
			holds = UnsignedAddOverflowBitVectorValue(actual, relation.Operand)
		case 2:
			holds = SignedAddOverflowBitVectorValue(actual, relation.Operand)
		case 3:
			holds = UnsignedSubOverflowBitVectorValue(actual, relation.Operand)
		case 4:
			holds = SignedSubOverflowBitVectorValue(actual, relation.Operand)
		case 5:
			holds = UnsignedMulOverflowBitVectorValue(actual, relation.Operand)
		case 6:
			holds = SignedMulOverflowBitVectorValue(actual, relation.Operand)
		case 7:
			holds = SignedDivOverflowBitVectorValue(actual, relation.Operand)
		case 8:
			holds = NegOverflowBitVectorValue(actual)
		}
		switch relation.Order {
		case 1:
			holds = CompareUnsignedBitVectorValue(actual, relation.Value) < 0
		case 2:
			holds = CompareUnsignedBitVectorValue(actual, relation.Value) <= 0
		case 3:
			holds = CompareSignedBitVectorValue(actual, relation.Value) < 0
		case 4:
			holds = CompareSignedBitVectorValue(actual, relation.Value) <= 0
		}
		if holds == relation.Negated {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	var model bitVectorModel
	for index := 0; index < assignmentCount; index++ {
		model.set(assignments[index].id, assignments[index].value)
	}
	return checkOutcome{status: checkSat, bitVectors: model}, true
}

func (encoder *bitVectorEncoder) boolean(term Term[BoolSort]) (int, bool) {
	switch value := term.(type) {
	case Bool:
		if value.Value {
			return encoder.trueLit, true
		}
		return -encoder.trueLit, true
	case Not:
		literal, ok := encoder.boolean(value.Value)
		return -literal, ok
	case And:
		literals := make([]int, len(value.Values))
		for index, item := range value.Values {
			literal, ok := encoder.boolean(item)
			if !ok {
				return 0, false
			}
			literals[index] = literal
		}
		return encoder.cnf.and(literals), true
	case BooleanConjunction:
		items, negated := value.values()
		literals := make([]int, len(items))
		for index, item := range items {
			literal, ok := encoder.boolean(item)
			if !ok {
				return 0, false
			}
			if negated[index] {
				literal = -literal
			}
			literals[index] = literal
		}
		return encoder.cnf.and(literals), true
	case Or:
		literals := make([]int, len(value.Values))
		for index, item := range value.Values {
			literal, ok := encoder.boolean(item)
			if !ok {
				return 0, false
			}
			literals[index] = literal
		}
		return encoder.cnf.or(literals), true
	case Implies:
		left, leftOK := encoder.boolean(value.Left)
		right, rightOK := encoder.boolean(value.Right)
		if !leftOK || !rightOK {
			return 0, false
		}
		return encoder.or2(-left, right), true
	case Iff:
		left, leftOK := encoder.boolean(value.Left)
		right, rightOK := encoder.boolean(value.Right)
		if !leftOK || !rightOK {
			return 0, false
		}
		return encoder.cnf.iff(left, right), true
	case Equal:
		if left, leftOK := value.Left.(Term[IntSort]); leftOK {
			if right, rightOK := value.Right.(Term[IntSort]); rightOK {
				if literal, recognized := encoder.integerConversionComparison(left, right, 0); recognized {
					return literal, true
				}
			}
		}
		left, leftOK := encoder.term(value.Left)
		right, rightOK := encoder.term(value.Right)
		if !leftOK || !rightOK || len(left) != len(right) {
			return 0, false
		}
		bits := make([]int, len(left))
		for index := range left {
			bits[index] = encoder.cnf.iff(left[index], right[index])
		}
		return encoder.cnf.and(bits), true
	case bitVectorUnsignedLess[BoolSort]:
		return encoder.order(value.left, value.right, false, value.orEqual)
	case bitVectorSignedLess[BoolSort]:
		return encoder.order(value.left, value.right, true, value.orEqual)
	case bitVectorUnsignedAddOverflow[BoolSort]:
		return encoder.addOverflow(value.left, value.right, false)
	case bitVectorSignedAddOverflow[BoolSort]:
		return encoder.addOverflow(value.left, value.right, true)
	case bitVectorUnsignedSubOverflow[BoolSort]:
		return encoder.subOverflow(value.left, value.right, false)
	case bitVectorSignedSubOverflow[BoolSort]:
		return encoder.subOverflow(value.left, value.right, true)
	case bitVectorUnsignedMulOverflow[BoolSort]:
		return encoder.mulOverflow(value.left, value.right, false)
	case bitVectorSignedMulOverflow[BoolSort]:
		return encoder.mulOverflow(value.left, value.right, true)
	case bitVectorSignedDivOverflow[BoolSort]:
		return encoder.signedDivOverflow(value.left, value.right)
	case bitVectorNegOverflow[BoolSort]:
		return encoder.negOverflow(value.value)
	case Less:
		return encoder.integerConversionComparison(value.Left, value.Right, -1)
	case LessEqual:
		return encoder.integerConversionComparison(value.Left, value.Right, -2)
	case BitVectorRelation:
		return encoder.boolean(expandBitVectorRelation(value))
	case BitVectorConjunction:
		literals := make([]int, 0, value.Count)
		for _, relation := range value.values() {
			literal, ok := encoder.boolean(expandBitVectorRelation(relation))
			if !ok {
				return 0, false
			}
			literals = append(literals, literal)
		}
		return encoder.cnf.and(literals), true
	case BitVectorIntegerRelation:
		return encoder.integerConversionComparisonRelation(value)
	case BitVectorMixedConjunction:
		literals := make([]int, 0, value.BitVectorCount+value.IntegerCount)
		for index := 0; index < value.BitVectorCount; index++ {
			literal, ok := encoder.boolean(value.BitVectors[index])
			if !ok {
				return 0, false
			}
			literals = append(literals, literal)
		}
		for index := 0; index < value.IntegerCount; index++ {
			literal, ok := encoder.boolean(value.Integers[index])
			if !ok {
				return 0, false
			}
			literals = append(literals, literal)
		}
		return encoder.cnf.and(literals), true
	}
	return 0, false
}

func (encoder *bitVectorEncoder) integerConversionComparisonRelation(value BitVectorIntegerRelation) (int, bool) {
	symbol := bitVectorSymbol[BitVecSort]{width: value.Width, iD: value.SymbolID}
	conversion := bitVectorToInteger[IntSort]{value: symbol, signed: value.Signed}
	literal, ok := encoder.conversionConstantComparison(conversion, value.Constant, int(value.Operation), value.Reverse)
	if value.Negated {
		literal = -literal
	}
	return literal, ok
}

func expandBitVectorRelation(relation BitVectorRelation) Term[BoolSort] {
	sourceWidth := relation.Width
	switch relation.Operation {
	case 11:
		sourceWidth = relation.ParameterA + 1
	case 12, 13:
		sourceWidth -= relation.ParameterA
	case 16:
		if relation.ParameterA > 0 {
			sourceWidth /= relation.ParameterA
		}
	}
	var actual Term[BitVecSort] = BitVecConst(sourceWidth, relation.SymbolID, "")
	operand := BitVectorTerm(relation.Operand)
	switch relation.Operation {
	case 1:
		actual = BitVecAdd(actual, operand)
	case 2:
		actual = BitVecSub(actual, operand)
	case 3:
		actual = BitVecMul(actual, operand)
	case 4:
		actual = BitVecSHL(actual, operand)
	case 5:
		actual = BitVecLSHR(actual, operand)
	case 6:
		actual = BitVecASHR(actual, operand)
	case 7:
		actual = BitVecUDiv(actual, operand)
	case 8:
		actual = BitVecURem(actual, operand)
	case 9:
		actual = BitVecSDiv(actual, operand)
	case 10:
		actual = BitVecSRem(actual, operand)
	case 11:
		actual = BitVecExtract(relation.ParameterA, relation.ParameterB, actual)
	case 12:
		actual = BitVecZeroExtend(relation.ParameterA, actual)
	case 13:
		actual = BitVecSignExtend(relation.ParameterA, actual)
	case 14:
		actual = BitVecRotateLeft(relation.ParameterA, actual)
	case 15:
		actual = BitVecRotateRight(relation.ParameterA, actual)
	case 16:
		actual = BitVecRepeat(relation.ParameterA, actual)
	}
	if relation.Masked {
		actual = BitVecAnd(actual, BitVectorTerm(relation.Mask))
	}
	constant := BitVectorTerm(relation.Value)
	var result Term[BoolSort]
	switch relation.Predicate {
	case 1:
		result = BitVecUAddOverflow(actual, operand)
	case 2:
		result = BitVecSAddOverflow(actual, operand)
	case 3:
		result = BitVecUSubOverflow(actual, operand)
	case 4:
		result = BitVecSSubOverflow(actual, operand)
	case 5:
		result = BitVecUMulOverflow(actual, operand)
	case 6:
		result = BitVecSMulOverflow(actual, operand)
	case 7:
		result = BitVecSDivOverflow(actual, operand)
	case 8:
		result = BitVecNegOverflow(actual)
	default:
		switch relation.Order {
		case 1:
			result = BitVecULT(actual, constant)
		case 2:
			result = BitVecULE(actual, constant)
		case 3:
			result = BitVecSLT(actual, constant)
		case 4:
			result = BitVecSLE(actual, constant)
		default:
			result = Equal{Left: actual, Right: constant}
		}
	}
	if relation.Negated {
		return Not{Value: result}
	}
	return result
}

func (encoder *bitVectorEncoder) term(term any) ([]int, bool) {
	switch value := term.(type) {
	case bitVector[BitVecSort]:
		bits := make([]int, value.value.Width())
		for index := range bits {
			bits[index] = -encoder.trueLit
			if value.value.Bit(index) {
				bits[index] = encoder.trueLit
			}
		}
		return bits, true
	case bitVectorSymbol[BitVecSort]:
		if prior, exists := encoder.widths[value.iD]; exists && prior != value.width {
			return nil, false
		}
		encoder.widths[value.iD] = value.width
		bits := make([]int, value.width)
		for index := range bits {
			key := bitVectorSymbolBit{id: value.iD, bit: index}
			literal, exists := encoder.symbols[key]
			if !exists {
				literal = encoder.cnf.variable()
				encoder.symbols[key] = literal
			}
			bits[index] = literal
		}
		return bits, true
	case bitVectorNot[BitVecSort]:
		bits, ok := encoder.term(value.value)
		if !ok {
			return nil, false
		}
		for index := range bits {
			bits[index] = -bits[index]
		}
		return bits, true
	case bitVectorAnd[BitVecSort]:
		return encoder.binary(value.left, value.right, encoder.and2)
	case bitVectorOr[BitVecSort]:
		return encoder.binary(value.left, value.right, encoder.or2)
	case bitVectorXor[BitVecSort]:
		return encoder.binary(value.left, value.right, encoder.xor2)
	case bitVectorAdd[BitVecSort]:
		left, leftOK := encoder.term(value.left)
		right, rightOK := encoder.term(value.right)
		if !leftOK || !rightOK || len(left) != len(right) {
			return nil, false
		}
		return encoder.addBits(left, right, -encoder.trueLit), true
	case bitVectorSub[BitVecSort]:
		left, leftOK := encoder.term(value.left)
		right, rightOK := encoder.term(value.right)
		if !leftOK || !rightOK || len(left) != len(right) {
			return nil, false
		}
		negated := make([]int, len(right))
		for index := range right {
			negated[index] = -right[index]
		}
		return encoder.addBits(left, negated, encoder.trueLit), true
	case bitVectorMul[BitVecSort]:
		left, leftOK := encoder.term(value.left)
		right, rightOK := encoder.term(value.right)
		if !leftOK || !rightOK || len(left) != len(right) {
			return nil, false
		}
		result := make([]int, len(left))
		for index := range result {
			result[index] = -encoder.trueLit
		}
		for shift := range right {
			partial := make([]int, len(left))
			for index := range partial {
				partial[index] = -encoder.trueLit
				if index >= shift {
					partial[index] = encoder.and2(left[index-shift], right[shift])
				}
			}
			result = encoder.addBits(result, partial, -encoder.trueLit)
		}
		return result, true
	case bitVectorShiftLeft[BitVecSort]:
		return encoder.shift(value.value, value.amount, 1)
	case bitVectorLogicalShiftRight[BitVecSort]:
		return encoder.shift(value.value, value.amount, 2)
	case bitVectorArithmeticShiftRight[BitVecSort]:
		return encoder.shift(value.value, value.amount, 3)
	case bitVectorUnsignedDiv[BitVecSort]:
		quotient, _, ok := encoder.divide(value.left, value.right, false)
		return quotient, ok
	case bitVectorUnsignedRem[BitVecSort]:
		_, remainder, ok := encoder.divide(value.left, value.right, false)
		return remainder, ok
	case bitVectorSignedDiv[BitVecSort]:
		quotient, _, ok := encoder.divide(value.left, value.right, true)
		return quotient, ok
	case bitVectorSignedRem[BitVecSort]:
		_, remainder, ok := encoder.divide(value.left, value.right, true)
		return remainder, ok
	case bitVectorConcat[BitVecSort]:
		first, firstOK := encoder.term(value.first)
		second, secondOK := encoder.term(value.second)
		if !firstOK || !secondOK || len(first) != value.firstWidth || len(second) != value.secondWidth {
			return nil, false
		}
		result := make([]int, 0, len(first)+len(second))
		result = append(result, second...)
		return append(result, first...), true
	case bitVectorExtract[BitVecSort]:
		bits, ok := encoder.term(value.value)
		if !ok || value.low < 0 || value.high < value.low || value.high >= len(bits) {
			return nil, false
		}
		return append([]int(nil), bits[value.low:value.high+1]...), true
	case bitVectorZeroExtend[BitVecSort]:
		bits, ok := encoder.term(value.value)
		if !ok || value.additional < 0 {
			return nil, false
		}
		result := append(make([]int, 0, len(bits)+value.additional), bits...)
		for range value.additional {
			result = append(result, -encoder.trueLit)
		}
		return result, true
	case bitVectorSignExtend[BitVecSort]:
		bits, ok := encoder.term(value.value)
		if !ok || len(bits) == 0 || value.additional < 0 {
			return nil, false
		}
		result := append(make([]int, 0, len(bits)+value.additional), bits...)
		for range value.additional {
			result = append(result, bits[len(bits)-1])
		}
		return result, true
	case bitVectorRotateLeft[BitVecSort]:
		bits, ok := encoder.term(value.value)
		if !ok || len(bits) == 0 || value.amount < 0 {
			return nil, false
		}
		amount := value.amount % len(bits)
		result := make([]int, len(bits))
		for index := range result {
			result[index] = bits[(index-amount+len(bits))%len(bits)]
		}
		return result, true
	case bitVectorRotateRight[BitVecSort]:
		bits, ok := encoder.term(value.value)
		if !ok || len(bits) == 0 || value.amount < 0 {
			return nil, false
		}
		amount := value.amount % len(bits)
		result := make([]int, len(bits))
		for index := range result {
			result[index] = bits[(index+amount)%len(bits)]
		}
		return result, true
	case bitVectorRepeat[BitVecSort]:
		bits, ok := encoder.term(value.value)
		if !ok || value.count <= 0 {
			return nil, false
		}
		result := make([]int, 0, len(bits)*value.count)
		for index := 0; index < value.count; index++ {
			result = append(result, bits...)
		}
		return result, true
	case sortedUnaryApplication[BitVecSort]:
		function, ok := value.function.(sortedUnaryFunctionValue[BitVecSort, BitVecSort])
		if !ok || value.rangeKind != 0 || function.domainKind <= 0 || function.rangeKind <= 0 {
			return nil, false
		}
		return encoder.bitVectorFunctionApplication(function.iD, value.argument, nil, function.domainKind, 0, function.rangeKind)
	case sortedBinaryApplication[BitVecSort]:
		function, ok := value.function.(sortedBinaryFunctionValue[BitVecSort, BitVecSort, BitVecSort])
		if !ok || value.rangeKind != 0 || function.firstKind <= 0 || function.secondKind <= 0 || function.rangeKind <= 0 {
			return nil, false
		}
		return encoder.bitVectorFunctionApplication(function.iD, value.first, value.second, function.firstKind, function.secondKind, function.rangeKind)
	case integerToBitVector[BitVecSort]:
		if constant, ok := exactIntegerConstant(value.value); ok {
			converted := IntegerToBitVectorValue(value.width, constant)
			return encoder.term(bitVector[BitVecSort]{value: converted})
		}
		if conversion, ok := value.value.(bitVectorToInteger[IntSort]); ok {
			bits, bitsOK := encoder.term(conversion.value)
			if !bitsOK || len(bits) == 0 {
				return nil, false
			}
			if value.width <= len(bits) {
				return append([]int(nil), bits[:value.width]...), true
			}
			fill := -encoder.trueLit
			if conversion.signed {
				fill = bits[len(bits)-1]
			}
			result := append(make([]int, 0, value.width), bits...)
			for len(result) < value.width {
				result = append(result, fill)
			}
			return result, true
		}
		return nil, false
	}
	return nil, false
}

func (encoder *bitVectorEncoder) bitVectorFunctionApplication(functionID int, firstTerm, secondTerm any, firstWidth, secondWidth, rangeWidth int) ([]int, bool) {
	first, firstOK := encoder.term(firstTerm)
	if !firstOK || len(first) != firstWidth {
		return nil, false
	}
	var second []int
	arity := uint8(1)
	if secondTerm != nil {
		var secondOK bool
		second, secondOK = encoder.term(secondTerm)
		if !secondOK || len(second) != secondWidth {
			return nil, false
		}
		arity = 2
	}
	result := make([]int, rangeWidth)
	for index := range result {
		result[index] = encoder.cnf.variable()
	}
	for _, prior := range encoder.applications {
		if prior.functionID != functionID || prior.arity != arity || len(prior.first) != len(first) || len(prior.second) != len(second) || len(prior.result) != rangeWidth {
			continue
		}
		equalities := make([]int, 0, len(first)+len(second))
		for index := range first {
			equalities = append(equalities, encoder.cnf.iff(first[index], prior.first[index]))
		}
		for index := range second {
			equalities = append(equalities, encoder.cnf.iff(second[index], prior.second[index]))
		}
		argumentsEqual := encoder.cnf.and(equalities)
		for index := range result {
			encoder.cnf.addClause(-argumentsEqual, -result[index], prior.result[index])
			encoder.cnf.addClause(-argumentsEqual, result[index], -prior.result[index])
		}
	}
	encoder.applications = append(encoder.applications, bitVectorEncodedApplication{functionID: functionID, arity: arity, first: first, second: second, result: result})
	return result, true
}

func (encoder *bitVectorEncoder) binary(leftTerm, rightTerm any, operation func(int, int) int) ([]int, bool) {
	left, leftOK := encoder.term(leftTerm)
	right, rightOK := encoder.term(rightTerm)
	if !leftOK || !rightOK || len(left) != len(right) {
		return nil, false
	}
	result := make([]int, len(left))
	for index := range left {
		result[index] = operation(left[index], right[index])
	}
	return result, true
}

func (encoder *bitVectorEncoder) addBits(left, right []int, carry int) []int {
	result, _ := encoder.addBitsCarry(left, right, carry)
	return result
}

func (encoder *bitVectorEncoder) addBitsCarry(left, right []int, carry int) ([]int, int) {
	result := make([]int, len(left))
	for index := range left {
		result[index] = encoder.xor2(encoder.xor2(left[index], right[index]), carry)
		carry = encoder.or2(encoder.or2(encoder.and2(left[index], right[index]), encoder.and2(left[index], carry)), encoder.and2(right[index], carry))
	}
	return result, carry
}

func (encoder *bitVectorEncoder) addOverflow(leftTerm, rightTerm any, signed bool) (int, bool) {
	left, leftOK := encoder.term(leftTerm)
	right, rightOK := encoder.term(rightTerm)
	if !leftOK || !rightOK || len(left) == 0 || len(left) != len(right) {
		return 0, false
	}
	result, carry := encoder.addBitsCarry(left, right, -encoder.trueLit)
	if !signed {
		return carry, true
	}
	sameSign := encoder.cnf.iff(left[len(left)-1], right[len(right)-1])
	changedSign := encoder.xor2(left[len(left)-1], result[len(result)-1])
	return encoder.and2(sameSign, changedSign), true
}

func (encoder *bitVectorEncoder) subOverflow(leftTerm, rightTerm any, signed bool) (int, bool) {
	left, leftOK := encoder.term(leftTerm)
	right, rightOK := encoder.term(rightTerm)
	if !leftOK || !rightOK || len(left) == 0 || len(left) != len(right) {
		return 0, false
	}
	if !signed {
		return encoder.lessBits(left, right), true
	}
	negated := make([]int, len(right))
	for index := range right {
		negated[index] = -right[index]
	}
	result := encoder.addBits(left, negated, encoder.trueLit)
	differentSigns := encoder.xor2(left[len(left)-1], right[len(right)-1])
	changedSign := encoder.xor2(left[len(left)-1], result[len(result)-1])
	return encoder.and2(differentSigns, changedSign), true
}

func (encoder *bitVectorEncoder) mulOverflow(leftTerm, rightTerm any, signed bool) (int, bool) {
	left, leftOK := encoder.term(leftTerm)
	right, rightOK := encoder.term(rightTerm)
	if !leftOK || !rightOK || len(left) == 0 || len(left) != len(right) {
		return 0, false
	}
	width := len(left)
	fillLeft, fillRight := -encoder.trueLit, -encoder.trueLit
	if signed {
		fillLeft, fillRight = left[width-1], right[width-1]
	}
	left = append(left, make([]int, width)...)
	right = append(right, make([]int, width)...)
	for index := width; index < 2*width; index++ {
		left[index], right[index] = fillLeft, fillRight
	}
	product := encoder.multiplyBits(left, right)
	if !signed {
		return encoder.cnf.or(product[width:]), true
	}
	equalities := make([]int, width)
	for index := range equalities {
		equalities[index] = encoder.cnf.iff(product[width+index], product[width-1])
	}
	return -encoder.cnf.and(equalities), true
}

func (encoder *bitVectorEncoder) multiplyBits(left, right []int) []int {
	result := make([]int, len(left))
	for index := range result {
		result[index] = -encoder.trueLit
	}
	for shift := range right {
		partial := make([]int, len(left))
		for index := range partial {
			partial[index] = -encoder.trueLit
			if index >= shift {
				partial[index] = encoder.and2(left[index-shift], right[shift])
			}
		}
		result = encoder.addBits(result, partial, -encoder.trueLit)
	}
	return result
}

func (encoder *bitVectorEncoder) signedDivOverflow(leftTerm, rightTerm any) (int, bool) {
	left, leftOK := encoder.term(leftTerm)
	right, rightOK := encoder.term(rightTerm)
	if !leftOK || !rightOK || len(left) == 0 || len(left) != len(right) {
		return 0, false
	}
	minimum := make([]int, len(left))
	minusOne := make([]int, len(right))
	for index := range left {
		minimum[index] = -left[index]
		minusOne[index] = right[index]
	}
	minimum[len(left)-1] = left[len(left)-1]
	return encoder.and2(encoder.cnf.and(minimum), encoder.cnf.and(minusOne)), true
}

func (encoder *bitVectorEncoder) negOverflow(valueTerm any) (int, bool) {
	value, ok := encoder.term(valueTerm)
	if !ok || len(value) == 0 {
		return 0, false
	}
	minimum := make([]int, len(value))
	for index := range value {
		minimum[index] = -value[index]
	}
	minimum[len(value)-1] = value[len(value)-1]
	return encoder.cnf.and(minimum), true
}

func (encoder *bitVectorEncoder) shift(valueTerm, amountTerm any, operation uint8) ([]int, bool) {
	value, valueOK := encoder.term(valueTerm)
	amount, amountOK := encoder.term(amountTerm)
	if !valueOK || !amountOK || len(value) == 0 || len(value) != len(amount) {
		return nil, false
	}
	selectors := make([]int, len(value))
	for shift := range selectors {
		selectors[shift] = encoder.equalConstant(amount, shift)
	}
	inRange := encoder.cnf.or(selectors)
	result := make([]int, len(value))
	for index := range result {
		choices := make([]int, 0, len(value)+1)
		for shift, selected := range selectors {
			source := -encoder.trueLit
			switch operation {
			case 1:
				if index >= shift {
					source = value[index-shift]
				}
			case 2:
				if index+shift < len(value) {
					source = value[index+shift]
				}
			case 3:
				source = value[len(value)-1]
				if index+shift < len(value) {
					source = value[index+shift]
				}
			}
			choices = append(choices, encoder.and2(selected, source))
		}
		if operation == 3 {
			choices = append(choices, encoder.and2(-inRange, value[len(value)-1]))
		}
		result[index] = encoder.cnf.or(choices)
	}
	return result, true
}

func (encoder *bitVectorEncoder) equalConstant(bits []int, value int) int {
	equalities := make([]int, len(bits))
	for index, bit := range bits {
		equalities[index] = -bit
		if value>>index&1 != 0 {
			equalities[index] = bit
		}
	}
	return encoder.cnf.and(equalities)
}

func (encoder *bitVectorEncoder) divide(leftTerm, rightTerm any, signed bool) ([]int, []int, bool) {
	left, leftOK := encoder.term(leftTerm)
	right, rightOK := encoder.term(rightTerm)
	if !leftOK || !rightOK || len(left) == 0 || len(left) != len(right) {
		return nil, nil, false
	}
	leftSign, rightSign := left[len(left)-1], right[len(right)-1]
	if signed {
		left = encoder.muxBits(leftSign, encoder.negateBits(left), left)
		right = encoder.muxBits(rightSign, encoder.negateBits(right), right)
	}
	quotient, remainder := encoder.unsignedDivide(left, right)
	if signed {
		quotient = encoder.muxBits(encoder.xor2(leftSign, rightSign), encoder.negateBits(quotient), quotient)
		remainder = encoder.muxBits(leftSign, encoder.negateBits(remainder), remainder)
	}
	return quotient, remainder, true
}

func (encoder *bitVectorEncoder) unsignedDivide(dividend, divisor []int) ([]int, []int) {
	width := len(dividend)
	quotient := make([]int, width)
	remainder := make([]int, width)
	for index := range remainder {
		remainder[index] = -encoder.trueLit
	}
	negatedDivisor := make([]int, width)
	for index := range divisor {
		negatedDivisor[index] = -divisor[index]
	}
	for index := width - 1; index >= 0; index-- {
		for bit := width - 1; bit > 0; bit-- {
			remainder[bit] = remainder[bit-1]
		}
		remainder[0] = dividend[index]
		ge := -encoder.lessBits(remainder, divisor)
		difference := encoder.addBits(remainder, negatedDivisor, encoder.trueLit)
		remainder = encoder.muxBits(ge, difference, remainder)
		quotient[index] = ge
	}
	return quotient, remainder
}

func (encoder *bitVectorEncoder) lessBits(left, right []int) int {
	equal, less := encoder.trueLit, -encoder.trueLit
	for index := len(left) - 1; index >= 0; index-- {
		less = encoder.or2(less, encoder.and2(equal, encoder.and2(-left[index], right[index])))
		equal = encoder.and2(equal, encoder.cnf.iff(left[index], right[index]))
	}
	return less
}

func (encoder *bitVectorEncoder) negateBits(value []int) []int {
	negated := make([]int, len(value))
	zero := make([]int, len(value))
	for index := range value {
		negated[index], zero[index] = -value[index], -encoder.trueLit
	}
	return encoder.addBits(negated, zero, encoder.trueLit)
}

func (encoder *bitVectorEncoder) muxBits(selector int, whenTrue, whenFalse []int) []int {
	result := make([]int, len(whenTrue))
	for index := range result {
		result[index] = encoder.or2(encoder.and2(selector, whenTrue[index]), encoder.and2(-selector, whenFalse[index]))
	}
	return result
}

func (encoder *bitVectorEncoder) and2(left, right int) int {
	result := encoder.cnf.variable()
	encoder.cnf.addClause(-result, left)
	encoder.cnf.addClause(-result, right)
	encoder.cnf.addClause(result, -left, -right)
	return result
}

func (encoder *bitVectorEncoder) or2(left, right int) int {
	result := encoder.cnf.variable()
	encoder.cnf.addClause(result, -left)
	encoder.cnf.addClause(result, -right)
	encoder.cnf.addClause(-result, left, right)
	return result
}

func (encoder *bitVectorEncoder) xor2(left, right int) int { return -encoder.cnf.iff(left, right) }

func (encoder *bitVectorEncoder) order(leftTerm, rightTerm any, signed, orEqual bool) (int, bool) {
	left, leftOK := encoder.term(leftTerm)
	right, rightOK := encoder.term(rightTerm)
	if !leftOK || !rightOK || len(left) == 0 || len(left) != len(right) {
		return 0, false
	}
	return encoder.orderBits(left, right, signed, orEqual), true
}

func (encoder *bitVectorEncoder) orderBits(left, right []int, signed, orEqual bool) int {
	equal := encoder.trueLit
	less := -encoder.trueLit
	for index := len(left) - 1; index >= 0; index-- {
		lessHere := encoder.and2(equal, encoder.and2(-left[index], right[index]))
		less = encoder.or2(less, lessHere)
		equal = encoder.and2(equal, encoder.cnf.iff(left[index], right[index]))
	}
	if signed {
		sameSign := encoder.cnf.iff(left[len(left)-1], right[len(right)-1])
		less = encoder.or2(encoder.and2(-sameSign, left[len(left)-1]), encoder.and2(sameSign, less))
	}
	if orEqual {
		less = encoder.or2(less, equal)
	}
	return less
}

func exactIntegerConstant(term any) (IntegerValue, bool) {
	switch value := term.(type) {
	case Integer:
		return NewIntegerValue(value.Value), true
	case integerExact[IntSort]:
		return value.value, true
	case Add:
		result := IntegerValue{}
		for _, item := range value.Values {
			next, ok := exactIntegerConstant(item)
			if !ok {
				return IntegerValue{}, false
			}
			result = AddIntegerValue(result, next)
		}
		return result, true
	case Subtract:
		left, leftOK := exactIntegerConstant(value.Left)
		right, rightOK := exactIntegerConstant(value.Right)
		if !leftOK || !rightOK {
			return IntegerValue{}, false
		}
		return SubIntegerValue(left, right), true
	case IntegerScale:
		operand, ok := exactIntegerConstant(value.Value)
		if !ok {
			return IntegerValue{}, false
		}
		return MultiplyIntegerValue(value.Coefficient, operand), true
	case IntegerDiv:
		dividend, ok := exactIntegerConstant(value.Dividend)
		if !ok {
			return IntegerValue{}, false
		}
		quotient, _, ok := DivModIntegerValue(dividend, value.Divisor)
		return quotient, ok
	case IntegerMod:
		dividend, ok := exactIntegerConstant(value.Dividend)
		if !ok {
			return IntegerValue{}, false
		}
		_, remainder, ok := DivModIntegerValue(dividend, value.Divisor)
		return remainder, ok
	}
	return IntegerValue{}, false
}

// ExactIntegerConstant exposes constant folding to compatibility layers while
// keeping symbolic integer terms opaque.
func ExactIntegerConstant(term Term[IntSort]) (IntegerValue, bool) {
	return exactIntegerConstant(term)
}

func (encoder *bitVectorEncoder) integerConversionComparison(left, right Term[IntSort], operation int) (int, bool) {
	if conversion, ok := left.(bitVectorToInteger[IntSort]); ok {
		if constant, constantOK := exactIntegerConstant(right); constantOK {
			return encoder.conversionConstantComparison(conversion, constant, operation, false)
		}
	}
	if conversion, ok := right.(bitVectorToInteger[IntSort]); ok {
		if constant, constantOK := exactIntegerConstant(left); constantOK {
			return encoder.conversionConstantComparison(conversion, constant, operation, true)
		}
	}
	return 0, false
}

func (encoder *bitVectorEncoder) conversionConstantComparison(conversion bitVectorToInteger[IntSort], constant IntegerValue, operation int, reverse bool) (int, bool) {
	bits, ok := encoder.term(conversion.value)
	if !ok || len(bits) == 0 {
		return 0, false
	}
	width := len(bits)
	minimum, maximum := IntegerValue{}, integerValueFromBig(new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), uint(width)), big.NewInt(1)))
	if conversion.signed {
		limit := new(big.Int).Lsh(big.NewInt(1), uint(width-1))
		minimum = integerValueFromBig(new(big.Int).Neg(new(big.Int).Set(limit)))
		maximum = integerValueFromBig(new(big.Int).Sub(limit, big.NewInt(1)))
	}
	below, above := CompareIntegerValue(constant, minimum) < 0, CompareIntegerValue(constant, maximum) > 0
	if operation == 0 {
		if below || above {
			return -encoder.trueLit, true
		}
		constantBits := encoder.constantBits(IntegerToBitVectorValue(width, constant))
		equalities := make([]int, width)
		for index := range bits {
			equalities[index] = encoder.cnf.iff(bits[index], constantBits[index])
		}
		return encoder.cnf.and(equalities), true
	}
	// operation -1 is left < right; -2 is left <= right.
	orEqual := operation == -2
	if !reverse {
		if below {
			return -encoder.trueLit, true
		}
		if above {
			return encoder.trueLit, true
		}
		constantBits := encoder.constantBits(IntegerToBitVectorValue(width, constant))
		return encoder.orderBits(bits, constantBits, conversion.signed, orEqual), true
	}
	if below {
		return encoder.trueLit, true
	}
	if above {
		return -encoder.trueLit, true
	}
	constantBits := encoder.constantBits(IntegerToBitVectorValue(width, constant))
	if orEqual {
		return -encoder.orderBits(bits, constantBits, conversion.signed, false), true
	}
	return -encoder.orderBits(bits, constantBits, conversion.signed, true), true
}

func (encoder *bitVectorEncoder) constantBits(value BitVectorValue) []int {
	bits := make([]int, value.Width())
	for index := range bits {
		bits[index] = -encoder.trueLit
		if value.Bit(index) {
			bits[index] = encoder.trueLit
		}
	}
	return bits
}

func evaluateBitVector(term any, model bitVectorModel, integers integerModel) (BitVectorValue, bool) {
	switch value := term.(type) {
	case bitVector[BitVecSort]:
		return value.value, true
	case bitVectorSymbol[BitVecSort]:
		return model.lookup(value.iD)
	case bitVectorNot[BitVecSort]:
		operand, ok := evaluateBitVector(value.value, model, integers)
		if !ok {
			return BitVectorValue{}, false
		}
		return NotBitVectorValue(operand), true
	case bitVectorAnd[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, AndBitVectorValue)
	case bitVectorOr[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, OrBitVectorValue)
	case bitVectorXor[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, XorBitVectorValue)
	case bitVectorAdd[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, AddBitVectorValue)
	case bitVectorSub[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, SubBitVectorValue)
	case bitVectorMul[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, MulBitVectorValue)
	case bitVectorShiftLeft[BitVecSort]:
		return evaluateBitVectorBinary(value.value, value.amount, model, integers, ShiftLeftBitVectorValue)
	case bitVectorLogicalShiftRight[BitVecSort]:
		return evaluateBitVectorBinary(value.value, value.amount, model, integers, LogicalShiftRightBitVectorValue)
	case bitVectorArithmeticShiftRight[BitVecSort]:
		return evaluateBitVectorBinary(value.value, value.amount, model, integers, ArithmeticShiftRightBitVectorValue)
	case bitVectorUnsignedDiv[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, UnsignedDivBitVectorValue)
	case bitVectorUnsignedRem[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, UnsignedRemBitVectorValue)
	case bitVectorSignedDiv[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, SignedDivBitVectorValue)
	case bitVectorSignedRem[BitVecSort]:
		return evaluateBitVectorBinary(value.left, value.right, model, integers, SignedRemBitVectorValue)
	case bitVectorConcat[BitVecSort]:
		return evaluateBitVectorBinary(value.first, value.second, model, integers, ConcatBitVectorValue)
	case bitVectorExtract[BitVecSort]:
		operand, ok := evaluateBitVector(value.value, model, integers)
		if !ok {
			return BitVectorValue{}, false
		}
		return ExtractBitVectorValue(operand, value.high, value.low), true
	case bitVectorZeroExtend[BitVecSort]:
		operand, ok := evaluateBitVector(value.value, model, integers)
		if !ok {
			return BitVectorValue{}, false
		}
		return ZeroExtendBitVectorValue(operand, value.additional), true
	case bitVectorSignExtend[BitVecSort]:
		operand, ok := evaluateBitVector(value.value, model, integers)
		if !ok {
			return BitVectorValue{}, false
		}
		return SignExtendBitVectorValue(operand, value.additional), true
	case bitVectorRotateLeft[BitVecSort]:
		operand, ok := evaluateBitVector(value.value, model, integers)
		if !ok {
			return BitVectorValue{}, false
		}
		return RotateLeftBitVectorValue(operand, value.amount), true
	case bitVectorRotateRight[BitVecSort]:
		operand, ok := evaluateBitVector(value.value, model, integers)
		if !ok {
			return BitVectorValue{}, false
		}
		return RotateRightBitVectorValue(operand, value.amount), true
	case bitVectorRepeat[BitVecSort]:
		operand, ok := evaluateBitVector(value.value, model, integers)
		if !ok {
			return BitVectorValue{}, false
		}
		return RepeatBitVectorValue(operand, value.count), true
	case sortedUnaryApplication[BitVecSort]:
		function, ok := value.function.(sortedUnaryFunctionValue[BitVecSort, BitVecSort])
		if !ok {
			return BitVectorValue{}, false
		}
		argument, ok := evaluateBitVector(value.argument, model, integers)
		if !ok {
			return BitVectorValue{}, false
		}
		return model.lookupApplication(function.iD, argument, BitVectorValue{}, 1)
	case sortedBinaryApplication[BitVecSort]:
		function, ok := value.function.(sortedBinaryFunctionValue[BitVecSort, BitVecSort, BitVecSort])
		if !ok {
			return BitVectorValue{}, false
		}
		first, firstOK := evaluateBitVector(value.first, model, integers)
		second, secondOK := evaluateBitVector(value.second, model, integers)
		if !firstOK || !secondOK {
			return BitVectorValue{}, false
		}
		return model.lookupApplication(function.iD, first, second, 2)
	case integerToBitVector[BitVecSort]:
		integerTerm, ok := value.value.(Term[IntSort])
		if !ok || value.width <= 0 {
			return BitVectorValue{}, false
		}
		integer, ok := evaluateInteger(integerTerm, booleanModel{}, integers, rationalModel{})
		if !ok {
			return BitVectorValue{}, false
		}
		return IntegerToBitVectorValue(value.width, integer), true
	}
	return BitVectorValue{}, false
}

func evaluateBitVectorBinary(leftTerm, rightTerm any, model bitVectorModel, integers integerModel, operation func(BitVectorValue, BitVectorValue) BitVectorValue) (BitVectorValue, bool) {
	left, leftOK := evaluateBitVector(leftTerm, model, integers)
	right, rightOK := evaluateBitVector(rightTerm, model, integers)
	if !leftOK || !rightOK || left.Width() != right.Width() {
		return BitVectorValue{}, false
	}
	return operation(left, right), true
}
