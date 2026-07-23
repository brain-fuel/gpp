package smt

import "strings"

// CompactStringReplaceEquality is the allocation-light representation of
// str.replace(x, source, replacement) = target for a direct symbol x and
// ground string operands.
type CompactStringReplaceEquality struct {
	SymbolID          int
	SymbolName        string
	Source            string
	SourceID          int
	SourceName        string
	SourceSymbol      bool
	Replacement       string
	ReplacementID     int
	ReplacementName   string
	ReplacementSymbol bool
	Target            string
	TargetID          int
	TargetName        string
	TargetSymbol      bool
	All               bool
}

func (CompactStringReplaceEquality) isTerm(BoolSort) {}

type groundStringReplaceConstraint struct {
	id                int
	equalityCount     int
	equalities        [4]CompactStringReplaceEquality
	overflow          []CompactStringReplaceEquality
	indexedCount      int
	indexed           [4]CompactStringIndexedEquality
	indexedOverflow   []CompactStringIndexedEquality
	predicateCount    int
	predicates        [4]Term[BoolSort]
	predicateOverflow []Term[BoolSort]
}

type groundStringReplaceConstraints struct {
	count    int
	inline   [4]groundStringReplaceConstraint
	overflow []groundStringReplaceConstraint
}

func (constraints *groundStringReplaceConstraints) at(index int) *groundStringReplaceConstraint {
	if constraints.overflow != nil {
		return &constraints.overflow[index]
	}
	return &constraints.inline[index]
}

func (constraints *groundStringReplaceConstraints) findOrAppend(id int) *groundStringReplaceConstraint {
	for index := 0; index < constraints.count; index++ {
		if constraints.at(index).id == id {
			return constraints.at(index)
		}
	}
	if constraints.overflow != nil {
		constraints.overflow = append(constraints.overflow, groundStringReplaceConstraint{id: id})
		constraints.count++
		return &constraints.overflow[constraints.count-1]
	}
	if constraints.count < len(constraints.inline) {
		constraints.inline[constraints.count].id = id
		constraints.count++
		return &constraints.inline[constraints.count-1]
	}
	constraints.overflow = make(
		[]groundStringReplaceConstraint, constraints.count, constraints.count*2,
	)
	copy(constraints.overflow, constraints.inline[:])
	constraints.overflow = append(constraints.overflow, groundStringReplaceConstraint{id: id})
	constraints.count++
	return &constraints.overflow[constraints.count-1]
}

func (constraint *groundStringReplaceConstraint) equalityAt(index int) CompactStringReplaceEquality {
	if constraint.overflow != nil {
		return constraint.overflow[index]
	}
	return constraint.equalities[index]
}

func (constraint *groundStringReplaceConstraint) append(equality CompactStringReplaceEquality) {
	if constraint.overflow != nil {
		constraint.overflow = append(constraint.overflow, equality)
		constraint.equalityCount++
		return
	}
	if constraint.equalityCount < len(constraint.equalities) {
		constraint.equalities[constraint.equalityCount] = equality
		constraint.equalityCount++
		return
	}
	constraint.overflow = make(
		[]CompactStringReplaceEquality, constraint.equalityCount, constraint.equalityCount*2,
	)
	copy(constraint.overflow, constraint.equalities[:])
	constraint.overflow = append(constraint.overflow, equality)
	constraint.equalityCount++
}

func (constraint *groundStringReplaceConstraint) indexedAt(index int) CompactStringIndexedEquality {
	if constraint.indexedOverflow != nil {
		return constraint.indexedOverflow[index]
	}
	return constraint.indexed[index]
}

func (constraint *groundStringReplaceConstraint) appendIndexed(equality CompactStringIndexedEquality) {
	if constraint.indexedOverflow != nil {
		constraint.indexedOverflow = append(constraint.indexedOverflow, equality)
		constraint.indexedCount++
		return
	}
	if constraint.indexedCount < len(constraint.indexed) {
		constraint.indexed[constraint.indexedCount] = equality
		constraint.indexedCount++
		return
	}
	constraint.indexedOverflow = make(
		[]CompactStringIndexedEquality, constraint.indexedCount, constraint.indexedCount*2,
	)
	copy(constraint.indexedOverflow, constraint.indexed[:])
	constraint.indexedOverflow = append(constraint.indexedOverflow, equality)
	constraint.indexedCount++
}

func (constraint *groundStringReplaceConstraint) predicateAt(index int) Term[BoolSort] {
	if constraint.predicateOverflow != nil {
		return constraint.predicateOverflow[index]
	}
	return constraint.predicates[index]
}

func (constraint *groundStringReplaceConstraint) appendPredicate(predicate Term[BoolSort]) {
	if constraint.predicateOverflow != nil {
		constraint.predicateOverflow = append(constraint.predicateOverflow, predicate)
		constraint.predicateCount++
		return
	}
	if constraint.predicateCount < len(constraint.predicates) {
		constraint.predicates[constraint.predicateCount] = predicate
		constraint.predicateCount++
		return
	}
	constraint.predicateOverflow = make(
		[]Term[BoolSort], constraint.predicateCount, constraint.predicateCount*2,
	)
	copy(constraint.predicateOverflow, constraint.predicates[:])
	constraint.predicateOverflow = append(constraint.predicateOverflow, predicate)
	constraint.predicateCount++
}

func solveGroundStringReplaceEqualities(assertions []Term[BoolSort]) (checkOutcome, bool) {
	var storage boundedWordEquationConjuncts
	for _, assertion := range assertions {
		appendBoundedWordEquationConjunct(assertion, &storage)
	}
	conjuncts := storage.values()
	if len(conjuncts) == 0 {
		return checkOutcome{}, false
	}
	assignments, contradiction := groundStringReplaceAssignments(conjuncts)
	if contradiction {
		return checkOutcome{status: checkUnsat}, true
	}
	var constraints groundStringReplaceConstraints
	for _, conjunct := range conjuncts {
		if ground, known := evaluateStringBoolean(conjunct, assignments, integerModel{}); known {
			if !ground {
				return checkOutcome{status: checkUnsat}, true
			}
			continue
		}
		equality, ok := groundStringReplaceEquality(conjunct, assignments)
		if ok {
			constraints.findOrAppend(equality.SymbolID).append(equality)
			continue
		}
		indexed, indexedOK := compactGroundIndexedStringEquality(conjunct)
		if indexedOK {
			constraints.findOrAppend(indexed.SymbolID).appendIndexed(indexed)
			continue
		}
		if !isBoundedWordEquationPredicate(conjunct) {
			return checkOutcome{}, false
		}
		var symbols stringSymbols
		collectStringSymbolsBoolean(conjunct, &symbols)
		unbound, count := unboundStringSymbol(symbols, assignments)
		if count != 1 {
			return checkOutcome{}, false
		}
		constraints.findOrAppend(unbound).appendPredicate(conjunct)
	}
	if constraints.count == 0 {
		return checkOutcome{}, false
	}
	for index := 0; index < constraints.count; index++ {
		if constraints.at(index).equalityCount == 0 {
			return checkOutcome{}, false
		}
	}
	model := assignments
	for index := 0; index < constraints.count; index++ {
		constraint := constraints.at(index)
		candidate, found, complete := groundStringReplacePreimage(constraint, assignments)
		if !complete {
			return checkOutcome{
				status: checkUnknown,
				reason: ResourceLimit{Limit: compactStringWordEquationSearchLimit},
			}, true
		}
		if !found {
			return checkOutcome{status: checkUnsat}, true
		}
		model.set(constraint.id, candidate)
	}
	return checkOutcome{status: checkSat, strings: model}, true
}

func unboundStringSymbol(symbols stringSymbols, model stringModel) (int, int) {
	id := 0
	count := 0
	for index := 0; index < symbols.count; index++ {
		candidate := symbols.inline[index]
		if _, bound := model.lookup(candidate); bound {
			continue
		}
		id = candidate
		count++
	}
	for candidate := range symbols.overflow {
		if _, bound := model.lookup(candidate); bound {
			continue
		}
		id = candidate
		count++
	}
	return id, count
}

func groundStringReplaceAssignments(
	conjuncts []Term[BoolSort],
) (stringModel, bool) {
	var model stringModel
	for pass := 0; pass < len(conjuncts)+1; pass++ {
		changed := false
		for _, conjunct := range conjuncts {
			switch value := conjunct.(type) {
			case Equal:
				var id int
				var assignment string
				var found bool
				if id, assignment, found = groundStringAssignmentSides(
					value.Left, value.Right, model,
				); !found {
					id, assignment, found = groundStringAssignmentSides(
						value.Right, value.Left, model,
					)
				}
				if found {
					if existing, bound := model.lookup(id); bound && existing != assignment {
						return model, true
					}
					changed = setExistingString(&model, id, assignment) || changed
				}
			case stringSystem:
				for _, relation := range value.system.relations() {
					if relation.Kind != CompactStringEqual || relation.Negated {
						continue
					}
					left, leftOK := evaluateCompactString(relation.Left, model)
					right, rightOK := evaluateCompactString(relation.Right, model)
					if relation.Left.Kind == compactStringSymbol && rightOK {
						if existing, bound := model.lookup(relation.Left.ID); bound && existing != right {
							return model, true
						}
						changed = setExistingString(&model, relation.Left.ID, right) || changed
					}
					if relation.Right.Kind == compactStringSymbol && leftOK {
						if existing, bound := model.lookup(relation.Right.ID); bound && existing != left {
							return model, true
						}
						changed = setExistingString(&model, relation.Right.ID, left) || changed
					}
				}
			}
		}
		if !changed {
			break
		}
	}
	return model, false
}

func groundStringAssignmentSides(
	symbol any, value any, model stringModel,
) (int, string, bool) {
	symbolTerm, ok := symbol.(Term[StringSort])
	if !ok {
		return 0, "", false
	}
	id, direct := stringSymbolID(symbolTerm)
	if !direct {
		return 0, "", false
	}
	valueTerm, ok := value.(Term[StringSort])
	if !ok {
		return 0, "", false
	}
	assignment, ground := evaluateString(valueTerm, model, integerModel{})
	return id, assignment, ground
}

func groundStringReplaceEquality(
	term Term[BoolSort], model stringModel,
) (CompactStringReplaceEquality, bool) {
	if compact, ok := term.(CompactStringReplaceEquality); ok {
		if compact.SourceSymbol {
			value, found := model.lookup(compact.SourceID)
			if !found {
				return CompactStringReplaceEquality{}, false
			}
			compact.Source = value
			compact.SourceSymbol = false
		}
		if compact.ReplacementSymbol {
			value, found := model.lookup(compact.ReplacementID)
			if !found {
				return CompactStringReplaceEquality{}, false
			}
			compact.Replacement = value
			compact.ReplacementSymbol = false
		}
		if compact.TargetSymbol {
			value, found := model.lookup(compact.TargetID)
			if !found {
				return CompactStringReplaceEquality{}, false
			}
			compact.Target = value
			compact.TargetSymbol = false
		}
		return compact, true
	}
	equality, ok := term.(Equal)
	if !ok {
		return CompactStringReplaceEquality{}, false
	}
	if result, ok := groundStringReplaceEqualitySides(equality.Left, equality.Right, model); ok {
		return result, true
	}
	return groundStringReplaceEqualitySides(equality.Right, equality.Left, model)
}

func groundStringReplaceEqualitySides(
	derived, target any, model stringModel,
) (CompactStringReplaceEquality, bool) {
	replacement, ok := derived.(stringReplace[StringSort])
	all := false
	if !ok {
		replacementAll, replaceAll := derived.(stringReplaceAll[StringSort])
		if !replaceAll {
			return CompactStringReplaceEquality{}, false
		}
		replacement = stringReplace[StringSort]{
			value:       replacementAll.value,
			source:      replacementAll.source,
			replacement: replacementAll.replacement,
		}
		all = true
	}
	id, symbol := stringSymbolID(replacement.value)
	source, sourceGround := evaluateString(replacement.source, model, integerModel{})
	newValue, replacementGround := evaluateString(replacement.replacement, model, integerModel{})
	targetTerm, targetString := target.(Term[StringSort])
	if !symbol || !sourceGround || !replacementGround || !targetString {
		return CompactStringReplaceEquality{}, false
	}
	targetValue, targetGround := evaluateString(targetTerm, model, integerModel{})
	if !targetGround {
		return CompactStringReplaceEquality{}, false
	}
	return CompactStringReplaceEquality{
		SymbolID:    id,
		Source:      source,
		Replacement: newValue,
		Target:      targetValue,
		All:         all,
	}, true
}

func groundStringReplacePreimage(
	constraint *groundStringReplaceConstraint,
	assignments stringModel,
) (string, bool, bool) {
	anchor := constraint.equalityAt(0)
	steps := 0
	try := func(candidate string) (string, bool, bool) {
		steps++
		if steps > compactStringWordEquationSearchLimit {
			return "", false, false
		}
		// The anchor candidate is constructed from its exact inverse rule, so
		// only the remaining equalities need evaluation. Besides avoiding
		// redundant work, this prevents strings.Replace from allocating a
		// throwaway copy on the common single-constraint path.
		for index := 1; index < constraint.equalityCount; index++ {
			equality := constraint.equalityAt(index)
			if !compactStringReplacementEquals(candidate, equality) {
				return "", false, true
			}
		}
		for index := 0; index < constraint.indexedCount; index++ {
			if !evaluateCompactIndexedStringEquality(
				constraint.indexedAt(index), candidate,
			) {
				return "", false, true
			}
		}
		if constraint.predicateCount > 0 {
			model := assignments
			model.set(constraint.id, candidate)
			for index := 0; index < constraint.predicateCount; index++ {
				accepted, known := evaluateStringBoolean(
					constraint.predicateAt(index), model, integerModel{},
				)
				if !known {
					return "", false, false
				}
				if !accepted {
					return "", false, true
				}
			}
		}
		return candidate, true, true
	}
	if forced, found := forcedGroundStringReplaceValue(constraint); found {
		if !compactStringReplacementEquals(forced, anchor) {
			return "", false, true
		}
		return try(forced)
	}
	if anchor.All {
		return groundStringReplaceAllPreimage(anchor, try)
	}
	if anchor.Source == "" {
		if !strings.HasPrefix(anchor.Target, anchor.Replacement) {
			return "", false, true
		}
		return try(anchor.Target[len(anchor.Replacement):])
	}
	if !strings.Contains(anchor.Target, anchor.Source) {
		if candidate, found, complete := try(anchor.Target); found || !complete {
			return candidate, found, complete
		}
	}
	if anchor.Replacement == "" {
		for offset := 0; offset <= len(anchor.Target); offset++ {
			if !stringWordEquationBoundary(anchor.Target, offset) {
				continue
			}
			prefix := anchor.Target[:offset]
			if strings.Contains(prefix, anchor.Source) {
				continue
			}
			candidate := prefix + anchor.Source + anchor.Target[offset:]
			if result, found, complete := try(candidate); found || !complete {
				return result, found, complete
			}
		}
		return "", false, true
	}
	for search := 0; search <= len(anchor.Target); {
		relative := strings.Index(anchor.Target[search:], anchor.Replacement)
		if relative < 0 {
			break
		}
		offset := search + relative
		prefix := anchor.Target[:offset]
		if !strings.Contains(prefix, anchor.Source) {
			candidate := prefix + anchor.Source + anchor.Target[offset+len(anchor.Replacement):]
			if result, found, complete := try(candidate); found || !complete {
				return result, found, complete
			}
		}
		search = offset + 1
	}
	return "", false, true
}

func forcedGroundStringReplaceValue(
	constraint *groundStringReplaceConstraint,
) (string, bool) {
	for index := 0; index < constraint.predicateCount; index++ {
		predicate := constraint.predicateAt(index)
		switch value := predicate.(type) {
		case Equal:
			if candidate, found := forcedGroundStringEqualitySides(
				constraint.id, value.Left, value.Right,
			); found {
				return candidate, true
			}
			if candidate, found := forcedGroundStringEqualitySides(
				constraint.id, value.Right, value.Left,
			); found {
				return candidate, true
			}
		case stringSystem:
			for _, relation := range value.system.relations() {
				if relation.Kind != CompactStringEqual || relation.Negated {
					continue
				}
				if candidate, found := forcedCompactStringRelationValue(
					constraint.id, relation.Left, relation.Right,
				); found {
					return candidate, true
				}
				if candidate, found := forcedCompactStringRelationValue(
					constraint.id, relation.Right, relation.Left,
				); found {
					return candidate, true
				}
			}
		}
	}
	return "", false
}

func forcedGroundStringEqualitySides(id int, symbol any, ground any) (string, bool) {
	symbolTerm, ok := symbol.(Term[StringSort])
	if !ok {
		return "", false
	}
	symbolID, direct := stringSymbolID(symbolTerm)
	if !direct || symbolID != id {
		return "", false
	}
	groundTerm, ok := ground.(Term[StringSort])
	if !ok {
		return "", false
	}
	return evaluateString(groundTerm, stringModel{}, integerModel{})
}

func forcedCompactStringRelationValue(
	id int, symbol CompactStringTerm, ground CompactStringTerm,
) (string, bool) {
	if symbol.Kind != compactStringSymbol || symbol.ID != id ||
		ground.Kind != compactStringLiteral {
		return "", false
	}
	return ground.Value, true
}

func compactStringReplacementEquals(
	candidate string, equality CompactStringReplaceEquality,
) bool {
	if !equality.All {
		return strings.Replace(
			candidate, equality.Source, equality.Replacement, 1,
		) == equality.Target
	}
	if equality.Source == "" {
		return candidate == equality.Target
	}
	inputOffset := 0
	targetOffset := 0
	for {
		relative := strings.Index(candidate[inputOffset:], equality.Source)
		if relative < 0 {
			return targetOffset <= len(equality.Target) &&
				candidate[inputOffset:] == equality.Target[targetOffset:]
		}
		match := inputOffset + relative
		literal := candidate[inputOffset:match]
		if targetOffset > len(equality.Target) ||
			!strings.HasPrefix(equality.Target[targetOffset:], literal) {
			return false
		}
		targetOffset += len(literal)
		if targetOffset > len(equality.Target) ||
			!strings.HasPrefix(equality.Target[targetOffset:], equality.Replacement) {
			return false
		}
		targetOffset += len(equality.Replacement)
		inputOffset = match + len(equality.Source)
	}
}

// groundStringReplaceAllPreimage enumerates the finite inverse parses induced
// by a nonempty replacement. Every target boundary can either be copied
// literally or consume one replacement and emit the source. Exact forward
// evaluation rejects parses whose copied text accidentally contains source.
//
// An empty replacement can have an unbounded inverse language. The identity
// candidate remains useful and exact; broader inversion is deliberately
// reported incomplete until the deletion transducer is represented directly.
func groundStringReplaceAllPreimage(
	anchor CompactStringReplaceEquality,
	try func(string) (string, bool, bool),
) (string, bool, bool) {
	accept := func(candidate string) (string, bool, bool) {
		if !compactStringReplacementEquals(candidate, anchor) {
			return "", false, true
		}
		return try(candidate)
	}
	if anchor.Source == "" {
		return accept(anchor.Target)
	}
	if candidate, found, complete := accept(anchor.Target); found || !complete {
		return candidate, found, complete
	}
	if anchor.Replacement == "" {
		candidate, found, complete := shortestStringDeletionPreimage(
			anchor.Target, anchor.Source,
		)
		if !found || !complete {
			return "", found, complete
		}
		if result, accepted, evaluated := accept(candidate); accepted || !evaluated {
			return result, accepted, evaluated
		}
		return enumerateFilteredStringDeletionPreimages(
			anchor.Target, anchor.Source, candidate, accept,
		)
	}
	// Replacing every visible output occurrence is the common inverse and
	// avoids constructing the search tree when it is already exact.
	direct := anchor.Source
	if anchor.Target != anchor.Replacement {
		direct = strings.ReplaceAll(anchor.Target, anchor.Replacement, anchor.Source)
	}
	if candidate, found, complete := accept(direct); found || !complete {
		return candidate, found, complete
	}
	states := 0
	return enumerateStringReplaceAllPreimages(anchor, accept, 0, "", &states)
}

type stringDeletionPath struct {
	previous int
	prefix   int
	output   int
	input    rune
}

func enumerateFilteredStringDeletionPreimages(
	target string,
	source string,
	skipCandidate string,
	try func(string) (string, bool, bool),
) (string, bool, bool) {
	var targetInline [16]rune
	var sourceInline [16]rune
	targetCodes, targetASCII := inlineASCIIStringCodePoints(target, targetInline[:])
	if !targetASCII {
		targetCodes = DecodeStringCodePoints(target)
	}
	sourceCodes, sourceASCII := inlineASCIIStringCodePoints(source, sourceInline[:])
	if !sourceASCII {
		sourceCodes = DecodeStringCodePoints(source)
	}
	if len(sourceCodes) == 0 {
		return try(target)
	}
	const inlineDeletionPaths = 32
	var inline [inlineDeletionPaths]stringDeletionPath
	paths := inline[:1]
	paths[0].previous = -1
	truncated := false
	for head := 0; head < len(paths); head++ {
		path := paths[head]
		if stringDeletionAcceptsEOF(
			sourceCodes, targetCodes, path.prefix, path.output,
		) {
			if stringDeletionASCIIPathEquals(paths, head, skipCandidate) {
				continue
			}
			candidate := stringDeletionPathCandidate(paths, head)
			if result, found, complete := try(candidate); found || !complete {
				return result, found, complete
			}
		}
		appendTransition := func(code rune) {
			nextPrefix, nextOutput, ok := stringDeletionTransition(
				sourceCodes, targetCodes, path.prefix, path.output, code,
			)
			if !ok {
				return
			}
			if len(paths) == compactStringWordEquationSearchLimit {
				truncated = true
				return
			}
			if len(paths) == cap(paths) {
				nextCapacity := cap(paths) * 2
				if nextCapacity > compactStringWordEquationSearchLimit {
					nextCapacity = compactStringWordEquationSearchLimit
				}
				overflow := make([]stringDeletionPath, len(paths), nextCapacity)
				copy(overflow, paths)
				paths = overflow
			}
			paths = append(paths, stringDeletionPath{
				previous: head,
				prefix:   nextPrefix,
				output:   nextOutput,
				input:    code,
			})
		}
		for index, code := range sourceCodes {
			if stringCodePointSeen(sourceCodes[:index], code) {
				continue
			}
			appendTransition(code)
		}
		for index, code := range targetCodes {
			if stringCodePointSeen(sourceCodes, code) ||
				stringCodePointSeen(targetCodes[:index], code) {
				continue
			}
			appendTransition(code)
		}
	}
	return "", false, !truncated
}

func stringDeletionASCIIPathEquals(
	paths []stringDeletionPath, index int, candidate string,
) bool {
	length := 0
	for current := index; current > 0; current = paths[current].previous {
		if paths[current].input >= 0x80 {
			return false
		}
		length++
	}
	if length != len(candidate) {
		return false
	}
	for offset := length - 1; offset >= 0; offset-- {
		if byte(paths[index].input) != candidate[offset] {
			return false
		}
		index = paths[index].previous
	}
	return true
}

func stringCodePointSeen(values []rune, target rune) bool {
	for _, value := range values {
		if value == target {
			return true
		}
	}
	return false
}

func stringDeletionPathCandidate(paths []stringDeletionPath, index int) string {
	length := 0
	ascii := true
	for current := index; current > 0; current = paths[current].previous {
		length++
		ascii = ascii && paths[current].input < 0x80
	}
	if ascii && length <= 64 {
		var inline [64]byte
		for offset := length - 1; offset >= 0; offset-- {
			inline[offset] = byte(paths[index].input)
			index = paths[index].previous
		}
		return string(inline[:length])
	}
	codes := make([]rune, length)
	for offset := length - 1; offset >= 0; offset-- {
		codes[offset] = paths[index].input
		index = paths[index].previous
	}
	var candidate strings.Builder
	for _, code := range codes {
		encoded, _ := EncodeStringCodePoint(int64(code))
		candidate.WriteString(encoded)
	}
	return candidate.String()
}

func shortestStringDeletionPreimage(
	target string, source string,
) (string, bool, bool) {
	var targetInline [16]rune
	var sourceInline [16]rune
	targetCodes, targetASCII := inlineASCIIStringCodePoints(target, targetInline[:])
	if !targetASCII {
		targetCodes = DecodeStringCodePoints(target)
	}
	sourceCodes, sourceASCII := inlineASCIIStringCodePoints(source, sourceInline[:])
	if !sourceASCII {
		sourceCodes = DecodeStringCodePoints(source)
	}
	if len(sourceCodes) == 0 {
		return target, true, true
	}
	if len(targetCodes)+1 > compactStringWordEquationSearchLimit/len(sourceCodes) {
		return "", false, false
	}
	stateCount := (len(targetCodes) + 1) * len(sourceCodes)
	const inlineDeletionStates = 32
	var visitedInline [inlineDeletionStates]bool
	var previousInline [inlineDeletionStates]int
	var inputInline [inlineDeletionStates]rune
	var queueInline [inlineDeletionStates]int
	var visited []bool
	var previous []int
	var input []rune
	var queue []int
	if stateCount <= inlineDeletionStates {
		visited = visitedInline[:stateCount]
		previous = previousInline[:stateCount]
		input = inputInline[:stateCount]
		queue = queueInline[:1]
	} else {
		visited = make([]bool, stateCount)
		previous = make([]int, stateCount)
		input = make([]rune, stateCount)
		queue = make([]int, 1, stateCount)
	}
	for index := range previous {
		previous[index] = -1
	}
	visited[0] = true
	queue[0] = 0
	for head := 0; head < len(queue); head++ {
		state := queue[head]
		output := state / len(sourceCodes)
		prefix := state % len(sourceCodes)
		if stringDeletionAcceptsEOF(sourceCodes, targetCodes, prefix, output) {
			return stringDeletionStateCandidate(previous, input, state), true, true
		}
		appendTransition := func(code rune) {
			nextPrefix, nextOutput, ok := stringDeletionTransition(
				sourceCodes, targetCodes, prefix, output, code,
			)
			if !ok {
				return
			}
			next := nextOutput*len(sourceCodes) + nextPrefix
			if visited[next] {
				return
			}
			visited[next] = true
			previous[next] = state
			input[next] = code
			queue = append(queue, next)
		}
		for _, code := range sourceCodes {
			appendTransition(code)
		}
		for _, code := range targetCodes {
			appendTransition(code)
		}
	}
	return "", false, true
}

func stringDeletionStateCandidate(previous []int, input []rune, state int) string {
	length := 0
	ascii := true
	for current := state; current != 0; current = previous[current] {
		length++
		ascii = ascii && input[current] < 0x80
	}
	if ascii && length <= 64 {
		var inline [64]byte
		for offset := length - 1; offset >= 0; offset-- {
			inline[offset] = byte(input[state])
			state = previous[state]
		}
		return string(inline[:length])
	}
	codes := make([]rune, length)
	for offset := length - 1; offset >= 0; offset-- {
		codes[offset] = input[state]
		state = previous[state]
	}
	var candidate strings.Builder
	for _, code := range codes {
		encoded, _ := EncodeStringCodePoint(int64(code))
		candidate.WriteString(encoded)
	}
	return candidate.String()
}

func inlineASCIIStringCodePoints(value string, storage []rune) ([]rune, bool) {
	if len(value) > len(storage) {
		return nil, false
	}
	for index := 0; index < len(value); index++ {
		if value[index] >= 0x80 {
			return nil, false
		}
		storage[index] = rune(value[index])
	}
	return storage[:len(value)], true
}

func stringDeletionAcceptsEOF(
	source []rune, target []rune, prefix int, output int,
) bool {
	if len(target)-output != prefix {
		return false
	}
	for index := 0; index < prefix; index++ {
		if source[index] != target[output+index] {
			return false
		}
	}
	return true
}

func stringDeletionTransition(
	source []rune,
	target []rune,
	prefix int,
	output int,
	code rune,
) (int, int, bool) {
	start := 0
	length := prefix + 1
	at := func(index int) rune {
		if index < prefix {
			return source[index]
		}
		return code
	}
	for start < length {
		remaining := length - start
		matchesPrefix := remaining <= len(source)
		for index := 0; matchesPrefix && index < remaining; index++ {
			matchesPrefix = at(start+index) == source[index]
		}
		if matchesPrefix {
			if remaining == len(source) {
				return 0, output, true
			}
			return remaining, output, true
		}
		if output >= len(target) || at(start) != target[output] {
			return 0, 0, false
		}
		output++
		start++
	}
	return 0, output, true
}

func enumerateStringReplaceAllPreimages(
	anchor CompactStringReplaceEquality,
	try func(string) (string, bool, bool),
	offset int,
	prefix string,
	states *int,
) (string, bool, bool) {
	*states = *states + 1
	if *states > compactStringWordEquationSearchLimit {
		return "", false, false
	}
	if offset == len(anchor.Target) {
		return try(prefix)
	}
	if strings.HasPrefix(anchor.Target[offset:], anchor.Replacement) {
		if candidate, found, complete := enumerateStringReplaceAllPreimages(
			anchor,
			try,
			offset+len(anchor.Replacement),
			prefix+anchor.Source,
			states,
		); found || !complete {
			return candidate, found, complete
		}
	}
	width := stringCodePointWidth(anchor.Target, offset)
	return enumerateStringReplaceAllPreimages(
		anchor,
		try,
		offset+width,
		prefix+anchor.Target[offset:offset+width],
		states,
	)
}
