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
	Kind       uint8
	SymbolID   int
	SymbolName string
	Offset     int64
	Length     int64
	Target     string
}

func (CompactStringIndexedEquality) isTerm(BoolSort) {}

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
	var storage boundedWordEquationConjuncts
	for _, assertion := range assertions {
		appendBoundedWordEquationConjunct(assertion, &storage)
	}
	conjuncts := storage.values()
	if len(conjuncts) == 0 {
		return checkOutcome{}, false
	}
	var constraints indexedStringConstraints
	for _, conjunct := range conjuncts {
		if ground, known := evaluateStringBoolean(conjunct, stringModel{}, integerModel{}); known {
			if !ground {
				return checkOutcome{status: checkUnsat}, true
			}
			continue
		}
		var id int
		if compact, ok := conjunct.(CompactStringIndexedEquality); ok {
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
		derived, target, ok := groundIndexedStringEquality(equality)
		if !ok {
			return checkOutcome{}, false
		}
		switch value := derived.(type) {
		case stringAt[StringSort]:
			id, ok = stringSymbolID(value.value)
			index, constant := integerConstant(value.index)
			if !ok || !constant {
				return checkOutcome{}, false
			}
			constraint := constraints.findOrAppend(id)
			if !applyStringAtEquality(constraint, index, target) {
				return checkOutcome{status: checkUnsat}, true
			}
		case stringSubstring[StringSort]:
			id, ok = stringSymbolID(value.value)
			offset, offsetConstant := integerConstant(value.offset)
			length, lengthConstant := integerConstant(value.length)
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
		valid, known := evaluateStringBoolean(conjunct, model, integerModel{})
		if !known || !valid {
			return checkOutcome{}, false
		}
	}
	return checkOutcome{status: checkSat, strings: model}, true
}

func groundIndexedStringEquality(equality Equal) (Term[StringSort], string, bool) {
	if left, ok := equality.Left.(Term[StringSort]); ok {
		if right, stringRight := equality.Right.(Term[StringSort]); stringRight {
			if target, ground := evaluateString(right, stringModel{}, integerModel{}); ground && isGroundIndexedStringTerm(left) {
				return left, target, true
			}
		}
	}
	if right, ok := equality.Right.(Term[StringSort]); ok {
		if left, stringLeft := equality.Left.(Term[StringSort]); stringLeft {
			if target, ground := evaluateString(left, stringModel{}, integerModel{}); ground && isGroundIndexedStringTerm(right) {
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
	derived, target, ok := groundIndexedStringEquality(equality)
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
