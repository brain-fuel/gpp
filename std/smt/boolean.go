package smt

// booleanEncoder introduces one Tseitin variable per compound expression.
// The resulting CNF is linear in the size of the authored term.
type booleanEncoder struct {
	nextVariable    int
	inlineCount     int
	inlineSymbols   [8]booleanSymbol
	overflowSymbols map[int]int
	inlineLiterals  [24]int
	inlineClauses   [12]cnfClause
	literals        []int
	clauses         []cnfClause
}

type booleanSymbol struct {
	id       int
	variable int
}

type cnfClause struct {
	start int
	end   int
}

func (encoder *booleanEncoder) initialize(termCount int) {
	if termCount < 1 {
		termCount = 1
	}
	encoder.literals = encoder.inlineLiterals[:0]
	encoder.clauses = encoder.inlineClauses[:0]
	if termCount*3 > cap(encoder.literals) {
		encoder.literals = make([]int, 0, termCount*3)
	}
	if termCount*2 > cap(encoder.clauses) {
		encoder.clauses = make([]cnfClause, 0, termCount*2)
	}
	if termCount > len(encoder.inlineSymbols) {
		encoder.overflowSymbols = make(map[int]int, termCount-len(encoder.inlineSymbols))
	}
}

func booleanTermSize(term Term[BoolSort]) int {
	size := 1
	switch value := term.(type) {
	case BooleanInlineCNF:
		return size + value.LiteralCount
	case BooleanClause:
		return size + len(value.Literals)
	case BooleanCNF:
		return size + len(value.Literals)
	case Not:
		return size + booleanTermSize(value.Value)
	case And:
		for _, item := range value.Values {
			size += booleanTermSize(item)
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			size += booleanTermSize(item)
		}
	case TheoryConjunction:
		items, _ := value.atomValues()
		for _, item := range items {
			size += booleanTermSize(item)
		}
		size += value.RealCount
	case Or:
		for _, item := range value.Values {
			size += booleanTermSize(item)
		}
	case Implies:
		size += booleanTermSize(value.Left) + booleanTermSize(value.Right)
	case Iff:
		size += booleanTermSize(value.Left) + booleanTermSize(value.Right)
	case If[BoolSort]:
		size += booleanTermSize(value.Condition) + booleanTermSize(value.Then) + booleanTermSize(value.Else)
	case Equal:
		if left, ok := value.Left.(Term[BoolSort]); ok {
			size += booleanTermSize(left)
		}
		if right, ok := value.Right.(Term[BoolSort]); ok {
			size += booleanTermSize(right)
		}
	}
	return size
}

func solveBooleanInlineCNF(cnf BooleanInlineCNF) checkOutcome {
	if cnf.LiteralCount < 0 || cnf.LiteralCount > len(cnf.Literals) || cnf.ClauseCount < 0 || cnf.ClauseCount > len(cnf.ClauseEnds) {
		return checkOutcome{status: checkUnknown, reason: UnsupportedTheory{Name: "invalid inline Boolean CNF bounds"}}
	}
	var assignment [65]int8
	var trail [64]int
	var used [65]bool
	maximum := 0
	start := 0
	for clause := 0; clause < cnf.ClauseCount; clause++ {
		end := cnf.ClauseEnds[clause]
		if end <= start || end > cnf.LiteralCount {
			return checkOutcome{status: checkUnknown, reason: UnsupportedTheory{Name: "invalid inline Boolean CNF clause"}}
		}
		for _, literal := range cnf.Literals[start:end] {
			variable := absCNF(literal)
			if variable == 0 || variable >= len(assignment) {
				return checkOutcome{status: checkUnknown, reason: UnsupportedTheory{Name: "inline Boolean CNF symbol ID outside 0..63"}}
			}
			if variable > maximum {
				maximum = variable
			}
			used[variable] = true
		}
		start = end
	}
	if start != cnf.LiteralCount {
		return checkOutcome{status: checkUnknown, reason: UnsupportedTheory{Name: "unclaimed inline Boolean CNF literals"}}
	}
	trailCount := 0
	if !searchBooleanInlineCNF(cnf, maximum, &used, &assignment, &trail, &trailCount) {
		return checkOutcome{status: checkUnsat}
	}
	var model booleanModel
	for variable := 1; variable <= maximum; variable++ {
		if used[variable] && assignment[variable] != 0 {
			model.set(variable-1, assignment[variable] > 0)
		}
	}
	return checkOutcome{status: checkSat, booleans: model}
}

func searchBooleanInlineCNF(cnf BooleanInlineCNF, maximum int, used *[65]bool, assignment *[65]int8, trail *[64]int, trailCount *int) bool {
	startTrail := *trailCount
	if !propagateBooleanInlineCNF(cnf, assignment, trail, trailCount) {
		rollbackBooleanInlineCNF(assignment, trail, trailCount, startTrail)
		return false
	}
	variable := 0
	for candidate := 1; candidate <= maximum; candidate++ {
		if used[candidate] && assignment[candidate] == 0 {
			variable = candidate
			break
		}
	}
	if variable == 0 {
		return true
	}
	branchTrail := *trailCount
	for _, literal := range [2]int{variable, -variable} {
		if assignBooleanInline(literal, assignment, trail, trailCount) && searchBooleanInlineCNF(cnf, maximum, used, assignment, trail, trailCount) {
			return true
		}
		rollbackBooleanInlineCNF(assignment, trail, trailCount, branchTrail)
	}
	rollbackBooleanInlineCNF(assignment, trail, trailCount, startTrail)
	return false
}

func propagateBooleanInlineCNF(cnf BooleanInlineCNF, assignment *[65]int8, trail *[64]int, trailCount *int) bool {
	for {
		changed := false
		start := 0
		for clause := 0; clause < cnf.ClauseCount; clause++ {
			end := cnf.ClauseEnds[clause]
			unassigned, unit, satisfied := 0, 0, false
			for _, literal := range cnf.Literals[start:end] {
				value := assignment[absCNF(literal)]
				if value == 0 {
					unassigned++
					unit = literal
				} else if (value > 0) == (literal > 0) {
					satisfied = true
					break
				}
			}
			start = end
			if satisfied {
				continue
			}
			if unassigned == 0 {
				return false
			}
			if unassigned == 1 {
				if !assignBooleanInline(unit, assignment, trail, trailCount) {
					return false
				}
				changed = true
			}
		}
		if !changed {
			return true
		}
	}
}

func assignBooleanInline(literal int, assignment *[65]int8, trail *[64]int, trailCount *int) bool {
	variable := absCNF(literal)
	value := int8(1)
	if literal < 0 {
		value = -1
	}
	if assignment[variable] != 0 {
		return assignment[variable] == value
	}
	assignment[variable] = value
	trail[*trailCount] = variable
	*trailCount++
	return true
}

func rollbackBooleanInlineCNF(assignment *[65]int8, trail *[64]int, trailCount *int, start int) {
	for *trailCount > start {
		*trailCount--
		assignment[trail[*trailCount]] = 0
	}
}

func (e *booleanEncoder) variable() int {
	e.nextVariable++
	return e.nextVariable
}

func (e *booleanEncoder) symbol(id int) int {
	for index := 0; index < e.inlineCount; index++ {
		if e.inlineSymbols[index].id == id {
			return e.inlineSymbols[index].variable
		}
	}
	if variable, ok := e.overflowSymbols[id]; ok {
		return variable
	}
	variable := e.variable()
	symbol := booleanSymbol{id: id, variable: variable}
	if e.inlineCount < len(e.inlineSymbols) {
		e.inlineSymbols[e.inlineCount] = symbol
		e.inlineCount++
	} else {
		if e.overflowSymbols == nil {
			e.overflowSymbols = make(map[int]int)
		}
		e.overflowSymbols[id] = variable
	}
	return variable
}

func (e *booleanEncoder) symbolCount() int {
	return e.inlineCount + len(e.overflowSymbols)
}

func (e *booleanEncoder) model(assignment cnfAssignment) booleanModel {
	var model booleanModel
	model.reserve(e.symbolCount())
	for index := 0; index < e.inlineCount; index++ {
		symbol := e.inlineSymbols[index]
		model.set(symbol.id, assignment.positive(symbol.variable))
	}
	for id, variable := range e.overflowSymbols {
		model.set(id, assignment.positive(variable))
	}
	return model
}

func (e *booleanEncoder) addClause(values ...int) {
	start := len(e.literals)
	e.literals = append(e.literals, values...)
	e.clauses = append(e.clauses, cnfClause{start: start, end: len(e.literals)})
}

func (e *booleanEncoder) and(values []int) int {
	result := e.variable()
	backward := make([]int, 1, len(values)+1)
	backward[0] = result
	for _, value := range values {
		e.addClause(-result, value)
		backward = append(backward, -value)
	}
	e.addClause(backward...)
	return result
}

func (e *booleanEncoder) or(values []int) int {
	result := e.variable()
	forward := make([]int, 1, len(values)+1)
	forward[0] = -result
	for _, value := range values {
		e.addClause(result, -value)
		forward = append(forward, value)
	}
	e.addClause(forward...)
	return result
}

func (e *booleanEncoder) iff(left, right int) int {
	result := e.variable()
	e.addClause(-result, -left, right)
	e.addClause(-result, left, -right)
	e.addClause(result, left, right)
	e.addClause(result, -left, -right)
	return result
}

func (e *booleanEncoder) term(term Term[BoolSort]) (int, bool) {
	switch value := term.(type) {
	case Bool:
		result := e.variable()
		if value.Value {
			e.addClause(result)
		} else {
			e.addClause(-result)
		}
		return result, true
	case BoolSymbol:
		return e.symbol(value.ID), true
	case BooleanVariable:
		return e.symbol(value.ID), true
	case NegatedBooleanVariable:
		return -e.symbol(value.ID), true
	case BooleanClause:
		items, ok := e.encodedBooleanLiterals(value.Literals)
		if !ok {
			return 0, false
		}
		return e.or(items), true
	case BooleanCNF:
		items, ok := e.encodedBooleanLiterals(value.Literals)
		if !ok {
			return 0, false
		}
		start := 0
		for _, end := range value.ClauseEnds {
			if end < start || end > len(items) {
				return 0, false
			}
			e.addClause(items[start:end]...)
			start = end
		}
		if start != len(items) {
			return 0, false
		}
		result := e.variable()
		e.addClause(result)
		return result, true
	case Not:
		result, ok := e.term(value.Value)
		return -result, ok
	case And:
		items := make([]int, len(value.Values))
		for index, item := range value.Values {
			literal, ok := e.term(item)
			if !ok {
				return 0, false
			}
			items[index] = literal
		}
		return e.and(items), true
	case BooleanConjunction:
		terms, negated := value.values()
		items := make([]int, len(terms))
		for index, item := range terms {
			literal, ok := e.term(item)
			if !ok {
				return 0, false
			}
			if negated[index] {
				literal = -literal
			}
			items[index] = literal
		}
		return e.and(items), true
	case TheoryConjunction:
		return 0, false
	case Or:
		items := make([]int, len(value.Values))
		for index, item := range value.Values {
			literal, ok := e.term(item)
			if !ok {
				return 0, false
			}
			items[index] = literal
		}
		return e.or(items), true
	case Implies:
		left, leftOK := e.term(value.Left)
		right, rightOK := e.term(value.Right)
		return e.or([]int{-left, right}), leftOK && rightOK
	case Iff:
		left, leftOK := e.term(value.Left)
		right, rightOK := e.term(value.Right)
		return e.iff(left, right), leftOK && rightOK
	case If[BoolSort]:
		condition, conditionOK := e.term(value.Condition)
		thenValue, thenOK := e.term(value.Then)
		elseValue, elseOK := e.term(value.Else)
		whenTrue := e.and([]int{condition, thenValue})
		whenFalse := e.and([]int{-condition, elseValue})
		return e.or([]int{whenTrue, whenFalse}), conditionOK && thenOK && elseOK
	case Equal:
		leftTerm, leftOK := value.Left.(Term[BoolSort])
		rightTerm, rightOK := value.Right.(Term[BoolSort])
		if !leftOK || !rightOK {
			return 0, false
		}
		left, leftEncoded := e.term(leftTerm)
		right, rightEncoded := e.term(rightTerm)
		return e.iff(left, right), leftEncoded && rightEncoded
	default:
		return 0, false
	}
}

func (e *booleanEncoder) encodedBooleanLiterals(values []int) ([]int, bool) {
	encoded := make([]int, len(values))
	for index, value := range values {
		if value == 0 {
			return nil, false
		}
		negated := value < 0
		id := value - 1
		if negated {
			id = -value - 1
		}
		literal := e.symbol(id)
		if negated {
			literal = -literal
		}
		encoded[index] = literal
	}
	return encoded, true
}

type cnfAssignment struct {
	wide   []int
	narrow []int8
}

func (assignment cnfAssignment) positive(variable int) bool {
	if assignment.narrow != nil {
		return assignment.narrow[variable] > 0
	}
	return assignment.wide[variable] > 0
}

func (assignment cnfAssignment) literalPositive(literal int) bool {
	if literal < 0 {
		return !assignment.positive(-literal)
	}
	return assignment.positive(literal)
}

func solveCNF(variableCount int, literals []int, clauses []cnfClause) (cnfAssignment, bool) {
	if len(clauses) < 64 {
		return solveCNFScanning(variableCount, literals, clauses)
	}
	solver, ok := newWatchedSolver(variableCount, literals, clauses)
	if !ok || !solver.search() {
		return cnfAssignment{}, false
	}
	return cnfAssignment{narrow: solver.assignment}, true
}

func solveCNFScanning(variableCount int, literals []int, clauses []cnfClause) (cnfAssignment, bool) {
	arena := make([]int, variableCount*2+1)
	assignment := arena[:variableCount+1]
	trail := arena[variableCount+1:][:0]
	if !searchCNFScanning(literals, clauses, assignment, &trail) {
		return cnfAssignment{}, false
	}
	return cnfAssignment{wide: assignment}, true
}

func searchCNFScanning(literals []int, clauses []cnfClause, assignment []int, trail *[]int) bool {
	start := len(*trail)
	if !propagateCNFScanning(literals, clauses, assignment, trail) {
		rollbackCNFScanning(assignment, trail, start)
		return false
	}
	variable := 0
	for candidate := 1; candidate < len(assignment); candidate++ {
		if assignment[candidate] == 0 {
			variable = candidate
			break
		}
	}
	if variable == 0 {
		return true
	}
	branchStart := len(*trail)
	for _, literal := range []int{variable, -variable} {
		if assignCNFScanning(literal, assignment, trail) && searchCNFScanning(literals, clauses, assignment, trail) {
			return true
		}
		rollbackCNFScanning(assignment, trail, branchStart)
	}
	rollbackCNFScanning(assignment, trail, start)
	return false
}

func propagateCNFScanning(literals []int, clauses []cnfClause, assignment []int, trail *[]int) bool {
	for {
		changed := false
		for _, clause := range clauses {
			unassigned := 0
			unit := 0
			satisfied := false
			for _, literal := range literals[clause.start:clause.end] {
				value := assignment[absCNF(literal)]
				if value == 0 {
					unassigned++
					unit = literal
				} else if (value > 0) == (literal > 0) {
					satisfied = true
					break
				}
			}
			if satisfied {
				continue
			}
			if unassigned == 0 {
				return false
			}
			if unassigned == 1 {
				if !assignCNFScanning(unit, assignment, trail) {
					return false
				}
				changed = true
			}
		}
		if !changed {
			return true
		}
	}
}

func assignCNFScanning(literal int, assignment []int, trail *[]int) bool {
	variable := absCNF(literal)
	value := 1
	if literal < 0 {
		value = -1
	}
	if assignment[variable] != 0 {
		return assignment[variable] == value
	}
	assignment[variable] = value
	*trail = append(*trail, variable)
	return true
}

func rollbackCNFScanning(assignment []int, trail *[]int, start int) {
	for _, variable := range (*trail)[start:] {
		assignment[variable] = 0
	}
	*trail = (*trail)[:start]
}

type watchedSolver struct {
	literals      []int
	clauses       []cnfClause
	assignment    []int8
	reason        []int
	watchA        []int
	watchB        []int
	heads         []int
	next          []int
	trail         []int
	limits        []int
	inlineLimits  [32]int
	seen          []bool
	levels        []int
	activity      []uint32
	activityStep  uint32
	inlineLearned [64]int
	queueHead     int
	conflicts     int
	learned       int
	backjumps     int
	restarts      int
	restartAfter  int
	sinceRestart  int
}

func newWatchedSolver(variableCount int, literals []int, clauses []cnfClause) (*watchedSolver, bool) {
	clauseCount := len(clauses)
	headCount := 2 * (variableCount + 1)
	metadataCount := clauseCount*4 + headCount
	variableSlots := variableCount + 1
	arena := make([]int, metadataCount+variableSlots+variableCount)
	watchA := arena[:clauseCount:clauseCount]
	watchB := arena[clauseCount : clauseCount*2 : clauseCount*2]
	heads := arena[clauseCount*2 : clauseCount*2+headCount]
	next := arena[clauseCount*2+headCount : clauseCount*4+headCount : clauseCount*4+headCount]
	reason := arena[metadataCount : metadataCount+variableSlots]
	trail := arena[metadataCount+variableSlots:][:0]
	for index := range reason {
		reason[index] = -1
	}
	for index := range heads {
		heads[index] = -1
	}
	for index := range next {
		next[index] = -1
	}
	solver := &watchedSolver{
		literals:   literals,
		clauses:    clauses,
		assignment: make([]int8, variableCount+1),
		reason:     reason,
		watchA:     watchA,
		watchB:     watchB,
		heads:      heads,
		next:       next,
		trail:      trail,
	}
	solver.limits = solver.inlineLimits[:0]
	solver.activityStep = 1
	solver.restartAfter = 64
	for index, clause := range clauses {
		length := clause.end - clause.start
		if length == 0 {
			return nil, false
		}
		solver.watchA[index] = clause.start
		solver.addWatch(index*2, literals[clause.start])
		if length == 1 {
			solver.watchB[index] = -1
			if !solver.assign(literals[clause.start], index) {
				return nil, false
			}
			continue
		}
		solver.watchB[index] = clause.start + 1
		solver.addWatch(index*2+1, literals[clause.start+1])
	}
	return solver, true
}

func (s *watchedSolver) addWatch(node, literal int) {
	index := watchIndex(literal)
	s.next[node] = s.heads[index]
	s.heads[index] = node
}

func (s *watchedSolver) search() bool {
	for {
		conflict := s.propagate()
		if conflict >= 0 {
			s.conflicts++
			s.sinceRestart++
			if len(s.limits) == 0 {
				return false
			}
			clause, backtrack := s.analyze(conflict)
			if backtrack < len(s.limits)-1 {
				s.backjumps++
			}
			s.rollbackLevel(backtrack)
			reason := s.addLearnedClause(clause)
			if !s.assign(clause[0], reason) {
				return false
			}
			continue
		}
		if s.sinceRestart >= s.restartAfter && len(s.limits) != 0 {
			s.rollbackLevel(0)
			s.sinceRestart = 0
			s.restartAfter += s.restartAfter / 2
			s.restarts++
			continue
		}
		variable := s.unassignedVariable()
		if variable == 0 {
			return true
		}
		s.limits = append(s.limits, len(s.trail))
		if !s.assign(variable, -1) {
			panic("smt: failed to make a fresh CDCL decision")
		}
	}
}

func (s *watchedSolver) propagate() int {
	for s.queueHead < len(s.trail) {
		literal := s.trail[s.queueHead]
		if conflict := s.propagateFalseWatch(-literal); conflict >= 0 {
			return conflict
		}
		s.queueHead++
	}
	return -1
}

func (s *watchedSolver) propagateFalseWatch(falseLiteral int) int {
	head := watchIndex(falseLiteral)
	node := s.heads[head]
	previous := -1
	for node >= 0 {
		next := s.next[node]
		clauseIndex := node / 2
		slot := node & 1
		currentPosition := s.watchA[clauseIndex]
		otherPosition := s.watchB[clauseIndex]
		if slot == 1 {
			currentPosition, otherPosition = otherPosition, currentPosition
		}
		if currentPosition < 0 || s.literals[currentPosition] != falseLiteral {
			panic("smt: corrupt watched-literal index")
		}
		if otherPosition >= 0 && s.literalValue(s.literals[otherPosition]) > 0 {
			previous = node
			node = next
			continue
		}

		replacement := -1
		clause := s.clauses[clauseIndex]
		for position := clause.start; position < clause.end; position++ {
			if position != currentPosition && position != otherPosition && s.literalValue(s.literals[position]) >= 0 {
				replacement = position
				break
			}
		}
		if replacement >= 0 {
			if slot == 0 {
				s.watchA[clauseIndex] = replacement
			} else {
				s.watchB[clauseIndex] = replacement
			}
			if previous < 0 {
				s.heads[head] = next
			} else {
				s.next[previous] = next
			}
			s.addWatch(node, s.literals[replacement])
			node = next
			continue
		}
		if otherPosition < 0 {
			return clauseIndex
		}
		otherLiteral := s.literals[otherPosition]
		if s.literalValue(otherLiteral) < 0 || !s.assign(otherLiteral, clauseIndex) {
			return clauseIndex
		}
		previous = node
		node = next
	}
	return -1
}

func (s *watchedSolver) literalValue(literal int) int8 {
	value := s.assignment[absCNF(literal)]
	if literal < 0 {
		return -value
	}
	return value
}

func (s *watchedSolver) assign(literal int, reason int) bool {
	variable := absCNF(literal)
	value := int8(1)
	if literal < 0 {
		value = -1
	}
	if s.assignment[variable] != 0 {
		return s.assignment[variable] == value
	}
	s.assignment[variable] = value
	s.reason[variable] = reason
	s.trail = append(s.trail, literal)
	return true
}

func (s *watchedSolver) rollbackLevel(level int) {
	start := len(s.trail)
	if level < len(s.limits) {
		start = s.limits[level]
	}
	for _, literal := range s.trail[start:] {
		variable := absCNF(literal)
		s.assignment[variable] = 0
		s.reason[variable] = -1
	}
	s.trail = s.trail[:start]
	s.limits = s.limits[:level]
	if s.queueHead > start {
		s.queueHead = start
	}
}

func (s *watchedSolver) unassignedVariable() int {
	best := 0
	for variable := 1; variable < len(s.assignment); variable++ {
		if s.assignment[variable] == 0 && (best == 0 || s.conflicts >= 64 && len(s.activity) != 0 && s.activity[variable] > s.activity[best]) {
			best = variable
		}
	}
	return best
}

func (s *watchedSolver) analyze(conflict int) ([]int, int) {
	learned := s.inlineLearned[:1]
	if s.seen == nil {
		s.seen = make([]bool, len(s.assignment))
		s.levels = make([]int, len(s.assignment))
	} else {
		clear(s.seen)
		clear(s.levels)
	}
	seen := s.seen
	levels := s.levels
	if s.conflicts >= 64 && s.activity == nil {
		s.activity = make([]uint32, len(s.assignment))
	}
	decisionLevel := 0
	nextLimit := 0
	for trailIndex, literal := range s.trail {
		for nextLimit < len(s.limits) && trailIndex >= s.limits[nextLimit] {
			decisionLevel++
			nextLimit++
		}
		levels[absCNF(literal)] = decisionLevel
	}
	currentLevel := len(s.limits)
	remaining := 0
	trailAt := len(s.trail) - 1
	clauseIndex := conflict
	pivot := 0
	for {
		clause := s.clauses[clauseIndex]
		for _, literal := range s.literals[clause.start:clause.end] {
			variable := absCNF(literal)
			if s.activity != nil {
				s.bumpActivity(variable)
			}
			if variable == pivot || seen[variable] || levels[variable] == 0 {
				continue
			}
			seen[variable] = true
			if levels[variable] == currentLevel {
				remaining++
			} else {
				learned = append(learned, literal)
			}
		}
		for trailAt >= 0 && !seen[absCNF(s.trail[trailAt])] {
			trailAt--
		}
		if trailAt < 0 {
			panic("smt: CDCL conflict analysis lost its implication path")
		}
		assigned := s.trail[trailAt]
		trailAt--
		pivot = absCNF(assigned)
		seen[pivot] = false
		remaining--
		if remaining == 0 {
			learned[0] = -assigned
			break
		}
		clauseIndex = s.reason[pivot]
		if clauseIndex < 0 {
			panic("smt: CDCL reached a decision before the first UIP")
		}
	}
	if s.activity != nil {
		s.activityStep += s.activityStep/16 + 1
	}
	backtrack := 0
	for _, literal := range learned[1:] {
		if level := levels[absCNF(literal)]; level > backtrack {
			backtrack = level
		}
	}
	return learned, backtrack
}

func (s *watchedSolver) bumpActivity(variable int) {
	if ^uint32(0)-s.activity[variable] < s.activityStep {
		for index := 1; index < len(s.activity); index++ {
			s.activity[index] >>= 1
		}
		s.activityStep = s.activityStep>>1 + 1
	}
	s.activity[variable] += s.activityStep
}

func (s *watchedSolver) addLearnedClause(values []int) int {
	if s.learned == 32 {
		s.reserveLearnedCapacity()
	}
	start := len(s.literals)
	s.literals = append(s.literals, values...)
	clauseIndex := len(s.clauses)
	s.clauses = append(s.clauses, cnfClause{start: start, end: len(s.literals)})
	s.watchA = append(s.watchA, start)
	s.watchB = append(s.watchB, -1)
	s.next = append(s.next, -1, -1)
	s.addWatch(clauseIndex*2, values[0])
	if len(values) > 1 {
		s.watchB[clauseIndex] = start + 1
		s.addWatch(clauseIndex*2+1, values[1])
	}
	s.learned++
	return clauseIndex
}

func (s *watchedSolver) reserveLearnedCapacity() {
	clauseCapacity := len(s.clauses) + 1024
	literalCapacity := len(s.literals) + 8192
	if cap(s.clauses) < clauseCapacity {
		values := make([]cnfClause, len(s.clauses), clauseCapacity)
		copy(values, s.clauses)
		s.clauses = values
	}
	if cap(s.literals) < literalCapacity {
		values := make([]int, len(s.literals), literalCapacity)
		copy(values, s.literals)
		s.literals = values
	}
	if cap(s.watchA) < clauseCapacity {
		values := make([]int, len(s.watchA), clauseCapacity)
		copy(values, s.watchA)
		s.watchA = values
	}
	if cap(s.watchB) < clauseCapacity {
		values := make([]int, len(s.watchB), clauseCapacity)
		copy(values, s.watchB)
		s.watchB = values
	}
	if cap(s.next) < clauseCapacity*2 {
		values := make([]int, len(s.next), clauseCapacity*2)
		copy(values, s.next)
		s.next = values
	}
}

func watchIndex(literal int) int {
	if literal < 0 {
		return -literal*2 + 1
	}
	return literal * 2
}

func absCNF(value int) int {
	if value < 0 {
		return -value
	}
	return value
}
