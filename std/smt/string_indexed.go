package smt

import "strings"

const (
	CompactStringAtEquality = iota
	CompactStringSubstringEquality
)

// CompactStringIndexedEquality is the allocation-light representation of a
// direct-symbol str.at or str.substr equality with ground indices and result.
// Kind is CompactStringAtEquality or CompactStringSubstringEquality; Offset
// is the at index or substring offset, and Length is used by substring.
type CompactStringIndexedEquality struct {
	Kind         uint8
	SymbolID     int
	SymbolName   string
	Offset       int64
	OffsetID     int
	OffsetName   string
	OffsetSymbol bool
	Length       int64
	LengthID     int
	LengthName   string
	LengthSymbol bool
	Target       string
}

func (CompactStringIndexedEquality) isTerm(BoolSort) {}

// CompactGroundIndexedStringFormula groups ground integer assignments with
// indexed-string equalities without allocating an interface-backed
// conjunction.
type CompactGroundIndexedStringFormula struct {
	AssignmentCount uint8
	Assignments     [4]IntegerLinearEquality
	EqualityCount   uint8
	Equalities      [4]CompactStringIndexedEquality
}

func (*CompactGroundIndexedStringFormula) isTerm(BoolSort) {}

// CompactStringIndexOfEquality represents
// str.indexof(text, needle, offset) = result for direct symbols.
type CompactStringIndexOfEquality struct {
	TextID     int
	TextName   string
	NeedleID   int
	NeedleName string
	OffsetID   int
	OffsetName string
	ResultID   int
	ResultName string
}

func (CompactStringIndexOfEquality) isTerm(BoolSort) {}

// CompactGroundStringEvaluationFormula groups direct ground assignments and
// derived index-of equalities without an allocating general conjunction.
type CompactGroundStringEvaluationFormula struct {
	StringAssignmentCount  uint8
	StringAssignments      [4]CompactStringRelation
	IntegerAssignmentCount uint8
	IntegerAssignments     [4]IntegerLinearEquality
	IndexOfCount           uint8
	IndexOf                [4]CompactStringIndexOfEquality
}

func (*CompactGroundStringEvaluationFormula) isTerm(BoolSort) {}

type indexedStringPlacement struct {
	index int64
	value string
}

type indexedStringConstraint struct {
	id                int
	minimum           int64
	maximum           int64
	hasMaximum        bool
	placementCount    int
	placements        [8]indexedStringPlacement
	placementOverflow []indexedStringPlacement
}

type indexedStringConstraints struct {
	count    int
	inline   [4]indexedStringConstraint
	overflow []indexedStringConstraint
}

func (constraints *indexedStringConstraints) at(index int) *indexedStringConstraint {
	if constraints.overflow != nil {
		return &constraints.overflow[index]
	}
	return &constraints.inline[index]
}

func (constraints *indexedStringConstraints) findOrAppend(id int) *indexedStringConstraint {
	for index := 0; index < constraints.count; index++ {
		if constraints.at(index).id == id {
			return constraints.at(index)
		}
	}
	if constraints.overflow != nil {
		constraints.overflow = append(constraints.overflow, indexedStringConstraint{id: id})
		constraints.count++
		return &constraints.overflow[constraints.count-1]
	}
	if constraints.count < len(constraints.inline) {
		constraints.inline[constraints.count].id = id
		constraints.count++
		return &constraints.inline[constraints.count-1]
	}
	constraints.overflow = make([]indexedStringConstraint, constraints.count, constraints.count*2)
	copy(constraints.overflow, constraints.inline[:])
	constraints.overflow = append(constraints.overflow, indexedStringConstraint{id: id})
	constraints.count++
	return &constraints.overflow[constraints.count-1]
}

func (constraint *indexedStringConstraint) placementAt(index int) indexedStringPlacement {
	if constraint.placementOverflow != nil {
		return constraint.placementOverflow[index]
	}
	return constraint.placements[index]
}

func (constraint *indexedStringConstraint) appendPlacement(placement indexedStringPlacement) {
	if constraint.placementOverflow != nil {
		constraint.placementOverflow = append(constraint.placementOverflow, placement)
		constraint.placementCount++
		return
	}
	if constraint.placementCount < len(constraint.placements) {
		constraint.placements[constraint.placementCount] = placement
		constraint.placementCount++
		return
	}
	constraint.placementOverflow = make(
		[]indexedStringPlacement, constraint.placementCount, constraint.placementCount*2,
	)
	copy(constraint.placementOverflow, constraint.placements[:])
	constraint.placementOverflow = append(constraint.placementOverflow, placement)
	constraint.placementCount++
}

const indexedStringModelCodePointLimit = 4096

// solveGroundIndexedStringEqualities is complete for conjunctions of positive
// equalities whose symbolic side is str.at(x, k) or str.substr(x, o, n), with
// a direct string symbol x and ground integer/result operands. Such equalities
// are exactly positional code-point requirements plus length bounds.
func solveGroundIndexedStringEqualities(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if len(assertions) == 1 {
		if compact, ok := assertions[0].(*CompactGroundIndexedStringFormula); ok {
			return solveCompactGroundIndexedStringFormula(compact), true
		}
		if _, evaluation := assertions[0].(*CompactGroundStringEvaluationFormula); evaluation {
			return checkOutcome{}, false
		}
	}
	var storage boundedWordEquationConjuncts
	for _, assertion := range assertions {
		appendBoundedWordEquationConjunct(assertion, &storage)
	}
	conjuncts := storage.values()
	if len(conjuncts) == 0 {
		return checkOutcome{}, false
	}
	integers, contradiction := groundIndexedIntegerAssignments(conjuncts)
	if contradiction {
		return checkOutcome{status: checkUnsat}, true
	}
	var constraints indexedStringConstraints
	for _, conjunct := range conjuncts {
		if id, value, assignment := groundIndexedIntegerAssignment(conjunct, integers); assignment {
			if existing, found := integers.lookup(id); found &&
				CompareIntegerValue(existing, value) == 0 {
				continue
			}
		}
		if ground, known := evaluateStringBoolean(conjunct, stringModel{}, integers); known {
			if !ground {
				return checkOutcome{status: checkUnsat}, true
			}
			continue
		}
		var id int
		if compact, ok := conjunct.(CompactStringIndexedEquality); ok {
			compact, ok = groundCompactIndexedStringEquality(compact, integers)
			if !ok {
				return checkOutcome{}, false
			}
			constraint := constraints.findOrAppend(compact.SymbolID)
			switch compact.Kind {
			case CompactStringAtEquality:
				if !applyStringAtEquality(constraint, compact.Offset, compact.Target) {
					return checkOutcome{status: checkUnsat}, true
				}
			case CompactStringSubstringEquality:
				if !applyStringSubstringEquality(constraint, compact.Offset, compact.Length, compact.Target) {
					return checkOutcome{status: checkUnsat}, true
				}
			default:
				return checkOutcome{}, false
			}
			continue
		}
		equality, ok := conjunct.(Equal)
		if !ok {
			return checkOutcome{}, false
		}
		derived, target, ok := groundIndexedStringEquality(equality, integers)
		if !ok {
			return checkOutcome{}, false
		}
		switch value := derived.(type) {
		case stringAt[StringSort]:
			id, ok = stringSymbolID(value.value)
			index, constant := evaluateStringOffset(value.index, integers)
			if !ok || !constant {
				return checkOutcome{}, false
			}
			constraint := constraints.findOrAppend(id)
			if !applyStringAtEquality(constraint, index, target) {
				return checkOutcome{status: checkUnsat}, true
			}
		case stringSubstring[StringSort]:
			id, ok = stringSymbolID(value.value)
			offset, offsetConstant := evaluateStringOffset(value.offset, integers)
			length, lengthConstant := evaluateStringOffset(value.length, integers)
			if !ok || !offsetConstant || !lengthConstant {
				return checkOutcome{}, false
			}
			constraint := constraints.findOrAppend(id)
			if !applyStringSubstringEquality(constraint, offset, length, target) {
				return checkOutcome{status: checkUnsat}, true
			}
		default:
			return checkOutcome{}, false
		}
	}
	if constraints.count == 0 {
		return checkOutcome{}, false
	}
	var model stringModel
	for index := 0; index < constraints.count; index++ {
		constraint := constraints.at(index)
		if constraint.hasMaximum && constraint.minimum > constraint.maximum {
			return checkOutcome{status: checkUnsat}, true
		}
		if constraint.minimum > indexedStringModelCodePointLimit {
			return checkOutcome{
				status: checkUnknown,
				reason: ResourceLimit{Limit: indexedStringModelCodePointLimit},
			}, true
		}
		var result strings.Builder
		for position := int64(0); position < constraint.minimum; position++ {
			value := "a"
			for placementIndex := 0; placementIndex < constraint.placementCount; placementIndex++ {
				placement := constraint.placementAt(placementIndex)
				if placement.index == position {
					value = placement.value
					break
				}
			}
			result.WriteString(value)
		}
		model.set(constraint.id, result.String())
	}
	for _, conjunct := range conjuncts {
		if id, value, assignment := groundIndexedIntegerAssignment(conjunct, integers); assignment {
			if existing, found := integers.lookup(id); found &&
				CompareIntegerValue(existing, value) == 0 {
				continue
			}
		}
		valid, known := evaluateStringBoolean(conjunct, model, integers)
		if !known || !valid {
			return checkOutcome{}, false
		}
	}
	return checkOutcome{status: checkSat, integers: integers, strings: model}, true
}

func solveCompactGroundIndexedStringFormula(
	formula *CompactGroundIndexedStringFormula,
) checkOutcome {
	var integers integerModel
	for index := 0; index < int(formula.AssignmentCount); index++ {
		assignment := formula.Assignments[index]
		outcome := solveCompactIntegerLinearEquality(assignment)
		if outcome.status != checkSat {
			return outcome
		}
		value, found := outcome.integers.lookup(assignment.ID)
		if !found {
			continue
		}
		if existing, assigned := integers.lookup(assignment.ID); assigned {
			if CompareIntegerValue(existing, value) != 0 {
				return checkOutcome{status: checkUnsat}
			}
			continue
		}
		integers.set(assignment.ID, value)
	}
	var constraints indexedStringConstraints
	for index := 0; index < int(formula.EqualityCount); index++ {
		equality, ground := groundCompactIndexedStringEquality(formula.Equalities[index], integers)
		if !ground {
			return checkOutcome{}
		}
		constraint := constraints.findOrAppend(equality.SymbolID)
		valid := false
		switch equality.Kind {
		case CompactStringAtEquality:
			valid = applyStringAtEquality(constraint, equality.Offset, equality.Target)
		case CompactStringSubstringEquality:
			valid = applyStringSubstringEquality(constraint, equality.Offset, equality.Length, equality.Target)
		}
		if !valid {
			return checkOutcome{status: checkUnsat}
		}
	}
	strings, outcome := indexedStringConstraintModel(&constraints)
	if outcome.status != checkSat {
		return outcome
	}
	for index := 0; index < int(formula.EqualityCount); index++ {
		equality, ground := groundCompactIndexedStringEquality(formula.Equalities[index], integers)
		if !ground {
			return checkOutcome{}
		}
		value, found := strings.lookup(equality.SymbolID)
		if !found || !evaluateCompactIndexedStringEquality(equality, value) {
			return checkOutcome{}
		}
	}
	return checkOutcome{status: checkSat, integers: integers, strings: strings}
}

func indexedStringConstraintModel(
	constraints *indexedStringConstraints,
) (stringModel, checkOutcome) {
	var model stringModel
	for index := 0; index < constraints.count; index++ {
		constraint := constraints.at(index)
		if constraint.hasMaximum && constraint.minimum > constraint.maximum {
			return stringModel{}, checkOutcome{status: checkUnsat}
		}
		if constraint.minimum > indexedStringModelCodePointLimit {
			return stringModel{}, checkOutcome{
				status: checkUnknown,
				reason: ResourceLimit{Limit: indexedStringModelCodePointLimit},
			}
		}
		var result strings.Builder
		for position := int64(0); position < constraint.minimum; position++ {
			value := "a"
			for placementIndex := 0; placementIndex < constraint.placementCount; placementIndex++ {
				placement := constraint.placementAt(placementIndex)
				if placement.index == position {
					value = placement.value
					break
				}
			}
			result.WriteString(value)
		}
		model.set(constraint.id, result.String())
	}
	return model, checkOutcome{status: checkSat}
}

func groundIndexedStringEquality(equality Equal, integers integerModel) (Term[StringSort], string, bool) {
	if left, ok := equality.Left.(Term[StringSort]); ok {
		if right, stringRight := equality.Right.(Term[StringSort]); stringRight {
			if target, ground := evaluateString(right, stringModel{}, integers); ground && isGroundIndexedStringTerm(left) {
				return left, target, true
			}
		}
	}
	if right, ok := equality.Right.(Term[StringSort]); ok {
		if left, stringLeft := equality.Left.(Term[StringSort]); stringLeft {
			if target, ground := evaluateString(left, stringModel{}, integers); ground && isGroundIndexedStringTerm(right) {
				return right, target, true
			}
		}
	}
	return nil, "", false
}

func compactGroundIndexedStringEquality(term Term[BoolSort]) (CompactStringIndexedEquality, bool) {
	if compact, ok := term.(CompactStringIndexedEquality); ok {
		return compact, true
	}
	equality, ok := term.(Equal)
	if !ok {
		return CompactStringIndexedEquality{}, false
	}
	derived, target, ok := groundIndexedStringEquality(equality, integerModel{})
	if !ok {
		return CompactStringIndexedEquality{}, false
	}
	switch value := derived.(type) {
	case stringAt[StringSort]:
		id, symbol := stringSymbolID(value.value)
		offset, constant := integerConstant(value.index)
		if !symbol || !constant {
			return CompactStringIndexedEquality{}, false
		}
		return CompactStringIndexedEquality{
			Kind: CompactStringAtEquality, SymbolID: id,
			Offset: offset, Target: target,
		}, true
	case stringSubstring[StringSort]:
		id, symbol := stringSymbolID(value.value)
		offset, offsetConstant := integerConstant(value.offset)
		length, lengthConstant := integerConstant(value.length)
		if !symbol || !offsetConstant || !lengthConstant {
			return CompactStringIndexedEquality{}, false
		}
		return CompactStringIndexedEquality{
			Kind: CompactStringSubstringEquality, SymbolID: id,
			Offset: offset, Length: length, Target: target,
		}, true
	default:
		return CompactStringIndexedEquality{}, false
	}
}

func groundIndexedIntegerAssignments(conjuncts []Term[BoolSort]) (integerModel, bool) {
	var model integerModel
	for pass := 0; pass < len(conjuncts); pass++ {
		changed := false
		for _, conjunct := range conjuncts {
			if compact, ok := conjunct.(IntegerLinearEquality); ok {
				if solveCompactIntegerLinearEquality(compact).status == checkUnsat {
					return integerModel{}, true
				}
			}
			id, value, assignment := groundIndexedIntegerAssignment(conjunct, model)
			if !assignment {
				continue
			}
			if existing, found := model.lookup(id); found {
				if CompareIntegerValue(existing, value) != 0 {
					return integerModel{}, true
				}
				continue
			}
			model.set(id, value)
			changed = true
		}
		if !changed {
			break
		}
	}
	return model, false
}

func groundIndexedIntegerAssignment(
	term Term[BoolSort], model integerModel,
) (int, IntegerValue, bool) {
	if compact, ok := term.(IntegerLinearEquality); ok {
		outcome := solveCompactIntegerLinearEquality(compact)
		if outcome.status != checkSat {
			return 0, IntegerValue{}, false
		}
		value, found := outcome.integers.lookup(compact.ID)
		return compact.ID, value, found
	}
	equality, ok := term.(Equal)
	if !ok {
		return 0, IntegerValue{}, false
	}
	if id, symbol := directIntegerSymbolID(equality.Left); symbol {
		if value, ground := evaluateStringIntegerExact(equality.Right, stringModel{}, model); ground {
			return id, value, true
		}
	}
	if id, symbol := directIntegerSymbolID(equality.Right); symbol {
		if value, ground := evaluateStringIntegerExact(equality.Left, stringModel{}, model); ground {
			return id, value, true
		}
	}
	return 0, IntegerValue{}, false
}

func directIntegerSymbolID(term any) (int, bool) {
	switch value := term.(type) {
	case IntSymbol:
		return value.ID, true
	case integerVariable[IntSort]:
		return value.iD, true
	default:
		return 0, false
	}
}

func evaluateCompactIndexedStringEquality(
	equality CompactStringIndexedEquality,
	value string,
) bool {
	var derived Term[StringSort]
	switch equality.Kind {
	case CompactStringAtEquality:
		derived = StringAt(StringVal(value), Integer{Value: equality.Offset})
	case CompactStringSubstringEquality:
		derived = StringSubstring(
			StringVal(value),
			Integer{Value: equality.Offset},
			Integer{Value: equality.Length},
		)
	default:
		return false
	}
	actual, known := evaluateString(derived, stringModel{}, integerModel{})
	return known && actual == equality.Target
}

func groundCompactIndexedStringEquality(
	equality CompactStringIndexedEquality, integers integerModel,
) (CompactStringIndexedEquality, bool) {
	if equality.OffsetSymbol {
		value, found := integers.lookup(equality.OffsetID)
		if !found {
			return CompactStringIndexedEquality{}, false
		}
		offset, fits := value.Int64()
		if !fits {
			return CompactStringIndexedEquality{}, false
		}
		equality.Offset = offset
		equality.OffsetSymbol = false
	}
	if equality.LengthSymbol {
		value, found := integers.lookup(equality.LengthID)
		if !found {
			return CompactStringIndexedEquality{}, false
		}
		length, fits := value.Int64()
		if !fits {
			return CompactStringIndexedEquality{}, false
		}
		equality.Length = length
		equality.LengthSymbol = false
	}
	return equality, true
}

func isGroundIndexedStringTerm(term Term[StringSort]) bool {
	switch term.(type) {
	case stringAt[StringSort], stringSubstring[StringSort]:
		return true
	default:
		return false
	}
}

func applyStringAtEquality(constraint *indexedStringConstraint, index int64, target string) bool {
	codePointCount := stringCodePointCount(target)
	if index < 0 {
		return codePointCount == 0
	}
	if codePointCount == 0 {
		return tightenIndexedStringMaximum(constraint, index)
	}
	if codePointCount != 1 || index == int64(^uint64(0)>>1) {
		return false
	}
	if !placeIndexedStringCodePoint(constraint, index, stringCodePointAt(target, 0)) {
		return false
	}
	return tightenIndexedStringMinimum(constraint, index+1)
}

func applyStringSubstringEquality(constraint *indexedStringConstraint, offset, length int64, target string) bool {
	count := stringCodePointCount(target)
	if offset < 0 || length <= 0 {
		return count == 0
	}
	if int64(count) > length || offset > int64(^uint64(0)>>1)-int64(count) {
		return false
	}
	if count == 0 {
		return tightenIndexedStringMaximum(constraint, offset)
	}
	targetOffset := 0
	for index := 0; index < count; index++ {
		value := stringCodePointAt(target, targetOffset)
		if !placeIndexedStringCodePoint(constraint, offset+int64(index), value) {
			return false
		}
		targetOffset += stringCodePointWidth(target, targetOffset)
	}
	end := offset + int64(count)
	if !tightenIndexedStringMinimum(constraint, end) {
		return false
	}
	if int64(count) < length {
		return tightenIndexedStringMaximum(constraint, end)
	}
	return true
}

func tightenIndexedStringMinimum(constraint *indexedStringConstraint, minimum int64) bool {
	if minimum > constraint.minimum {
		constraint.minimum = minimum
	}
	return !constraint.hasMaximum || constraint.minimum <= constraint.maximum
}

func tightenIndexedStringMaximum(constraint *indexedStringConstraint, maximum int64) bool {
	if !constraint.hasMaximum || maximum < constraint.maximum {
		constraint.maximum = maximum
		constraint.hasMaximum = true
	}
	return constraint.minimum <= constraint.maximum
}

func placeIndexedStringCodePoint(constraint *indexedStringConstraint, index int64, value string) bool {
	for placementIndex := 0; placementIndex < constraint.placementCount; placementIndex++ {
		placement := constraint.placementAt(placementIndex)
		if placement.index == index {
			return placement.value == value
		}
	}
	constraint.appendPlacement(indexedStringPlacement{
		index: index,
		value: value,
	})
	return true
}

func stringCodePointAt(value string, offset int) string {
	width := stringCodePointWidth(value, offset)
	if width == 1 && value[offset] >= 0x80 {
		return "\uFFFD"
	}
	return value[offset : offset+width]
}
