package smt

// RealUnaryEquality is the compact normalized equality of two applications
// of Real->Real uninterpreted functions to named real symbols.
type RealUnaryEquality struct {
	LeftFunctionID  int
	LeftArgumentID  int
	RightFunctionID int
	RightArgumentID int
}

func (RealUnaryEquality) isTerm(BoolSort) {}

// UninterpretedEUFTerm is the compact, name-independent representation of a
// ground uninterpreted-sort symbol or an application whose arguments are
// symbols. Kind 1 is a symbol, 2 a unary application, and 3 a binary
// application. The ordinary typed EUF AST remains the general fallback.
type UninterpretedEUFTerm struct {
	Kind         uint8
	SortID       int
	SymbolID     int
	FunctionID   int
	FirstSortID  int
	SecondSortID int
	FirstID      int
	SecondID     int
}

type UninterpretedEUFRelation struct {
	Left    UninterpretedEUFTerm
	Right   UninterpretedEUFTerm
	Negated bool
}

func (UninterpretedEUFRelation) isTerm(BoolSort) {}

type UninterpretedEUFConjunction struct {
	Count    int
	Inline   [4]UninterpretedEUFRelation
	Overflow []UninterpretedEUFRelation
}

func (UninterpretedEUFConjunction) isTerm(BoolSort) {}

func (value UninterpretedEUFConjunction) values() []UninterpretedEUFRelation {
	if value.Overflow != nil {
		return value.Overflow[:value.Count]
	}
	return value.Inline[:value.Count]
}

// The EUF foundation intentionally recognizes conjunctions of ground
// equalities and disequalities. Congruence closure is independent of symbol
// spelling and uses the retained sort/function identities.
type eufNode struct {
	kind         uint8
	sortID       int
	symbolID     int
	functionID   int
	firstSortID  int
	secondSortID int
	first        int
	second       int
}

type eufPair struct {
	left  int
	right int
}

type eufProblem struct {
	nodes             []eufNode
	parents           []int
	ranks             []uint8
	equalities        []eufPair
	disequality       []eufPair
	unsat             bool
	inlineNodes       [8]eufNode
	inlineParents     [8]int
	inlineRanks       [8]uint8
	inlineEqualities  [4]eufPair
	inlineDisequality [4]eufPair
}

func containsEUF(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			if containsEUF(item) {
				return true
			}
		}
	case BooleanConjunction:
		terms, _ := value.values()
		for _, item := range terms {
			if containsEUF(item) {
				return true
			}
		}
	case TheoryConjunction:
		if value.UnaryComparisonCount != 0 || value.BinaryComparisonCount != 0 {
			return true
		}
		terms, _ := value.atomValues()
		for _, item := range terms {
			if containsEUF(item) {
				return true
			}
		}
	case Or:
		for _, item := range value.Values {
			if containsEUF(item) {
				return true
			}
		}
	case Not:
		return containsEUF(value.Value)
	case Implies:
		return containsEUF(value.Left) || containsEUF(value.Right)
	case Iff:
		return containsEUF(value.Left) || containsEUF(value.Right)
	case If[BoolSort]:
		return containsEUF(value.Condition) || containsEUF(value.Then) || containsEUF(value.Else)
	case Equal:
		return isEUFTerm(value.Left) || isEUFTerm(value.Right)
	case RealUnaryEquality:
		return true
	case UninterpretedEUFRelation, UninterpretedEUFConjunction:
		return true
	case BitVectorEUFRelation:
		return true
	case BitVectorEUFConjunction:
		return true
	case RealUnaryComparison:
		return true
	case RealBinaryComparison:
		return true
	}
	return false
}

func (problem *eufProblem) compactUninterpretedTerm(term UninterpretedEUFTerm) (int, bool) {
	switch term.Kind {
	case 1:
		return problem.ensureNode(eufNode{sortID: term.SortID, symbolID: term.SymbolID}), true
	case 2:
		argument := problem.ensureNode(eufNode{sortID: term.FirstSortID, symbolID: term.FirstID})
		return problem.ensureNode(eufNode{kind: 1, sortID: term.SortID, functionID: term.FunctionID, firstSortID: term.FirstSortID, first: argument, second: -1}), true
	case 3:
		first := problem.ensureNode(eufNode{sortID: term.FirstSortID, symbolID: term.FirstID})
		second := problem.ensureNode(eufNode{sortID: term.SecondSortID, symbolID: term.SecondID})
		return problem.ensureNode(eufNode{kind: 2, sortID: term.SortID, functionID: term.FunctionID, firstSortID: term.FirstSortID, secondSortID: term.SecondSortID, first: first, second: second}), true
	default:
		return 0, false
	}
}

func (problem *eufProblem) compactBitVectorTerm(term BitVectorEUFTerm) (int, bool) {
	sortID := bitVectorEUFSort(term.Width)
	switch term.Kind {
	case 1:
		return problem.ensureNode(eufNode{sortID: sortID, symbolID: term.SymbolID}), true
	case 2:
		argumentSort := bitVectorEUFSort(term.FirstWidth)
		argument := problem.ensureNode(eufNode{sortID: argumentSort, symbolID: term.FirstID})
		return problem.ensureNode(eufNode{kind: 1, sortID: sortID, functionID: term.FunctionID, firstSortID: argumentSort, first: argument, second: -1}), true
	default:
		return 0, false
	}
}

func isEUFTerm(term any) bool {
	switch term.(type) {
	case uninterpretedValue[UninterpretedSort], unaryApplication[UninterpretedSort], binaryApplication[UninterpretedSort], sortedUnaryApplication[RealSort], sortedBinaryApplication[RealSort], sortedUnaryApplication[BitVecSort], sortedBinaryApplication[BitVecSort]:
		return true
	default:
		return false
	}
}

func solveEUFAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	return solveEUFPolarized(assertions, nil)
}

func solveEUFPolarized(assertions []Term[BoolSort], negated []bool) (checkOutcome, bool) {
	problem := eufProblem{}
	problem.initialize()
	for index, assertion := range assertions {
		polarity := false
		if negated != nil {
			polarity = negated[index]
		}
		if !problem.boolean(assertion, polarity) {
			return checkOutcome{}, false
		}
	}
	return problem.solve()
}

func (problem *eufProblem) initialize() {
	problem.nodes = problem.inlineNodes[:0]
	problem.parents = problem.inlineParents[:0]
	problem.ranks = problem.inlineRanks[:0]
	problem.equalities = problem.inlineEqualities[:0]
	problem.disequality = problem.inlineDisequality[:0]
}

func (problem *eufProblem) solve() (checkOutcome, bool) {
	for _, equality := range problem.equalities {
		problem.union(equality.left, equality.right)
	}
	if problem.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	for {
		changed := false
		for left := 0; left < len(problem.nodes); left++ {
			leftNode := problem.nodes[left]
			if leftNode.kind != 1 && leftNode.kind != 2 {
				continue
			}
			for right := left + 1; right < len(problem.nodes); right++ {
				rightNode := problem.nodes[right]
				if rightNode.kind != leftNode.kind || leftNode.functionID != rightNode.functionID || leftNode.firstSortID != rightNode.firstSortID || leftNode.secondSortID != rightNode.secondSortID || leftNode.sortID != rightNode.sortID {
					continue
				}
				argumentsEqual := problem.find(leftNode.first) == problem.find(rightNode.first)
				if leftNode.kind == 2 {
					argumentsEqual = argumentsEqual && problem.find(leftNode.second) == problem.find(rightNode.second)
				}
				if argumentsEqual && problem.find(left) != problem.find(right) {
					problem.union(left, right)
					changed = true
				}
			}
		}
		if !changed {
			break
		}
	}
	for _, disequality := range problem.disequality {
		if problem.find(disequality.left) == problem.find(disequality.right) {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	return checkOutcome{status: checkSat}, true
}

func (problem *eufProblem) boolean(term Term[BoolSort], negated bool) bool {
	switch value := term.(type) {
	case Bool:
		problem.unsat = problem.unsat || value.Value == negated
		return true
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
		terms, polarities := value.values()
		for index, item := range terms {
			if !problem.boolean(item, polarities[index]) {
				return false
			}
		}
		return true
	case Not:
		return problem.boolean(value.Value, !negated)
	case Equal:
		left, leftOK := problem.term(value.Left)
		right, rightOK := problem.term(value.Right)
		if !leftOK || !rightOK || problem.nodes[left].sortID != problem.nodes[right].sortID {
			return false
		}
		pair := eufPair{left: left, right: right}
		if negated {
			problem.disequality = append(problem.disequality, pair)
		} else {
			problem.equalities = append(problem.equalities, pair)
		}
		return true
	case RealUnaryEquality:
		left := problem.realUnaryApplication(value.LeftFunctionID, value.LeftArgumentID)
		right := problem.realUnaryApplication(value.RightFunctionID, value.RightArgumentID)
		pair := eufPair{left: left, right: right}
		if negated {
			problem.disequality = append(problem.disequality, pair)
		} else {
			problem.equalities = append(problem.equalities, pair)
		}
		return true
	case UninterpretedEUFRelation:
		left, leftOK := problem.compactUninterpretedTerm(value.Left)
		right, rightOK := problem.compactUninterpretedTerm(value.Right)
		if !leftOK || !rightOK || problem.nodes[left].sortID != problem.nodes[right].sortID {
			return false
		}
		pair := eufPair{left: left, right: right}
		if value.Negated != negated {
			problem.disequality = append(problem.disequality, pair)
		} else {
			problem.equalities = append(problem.equalities, pair)
		}
		return true
	case UninterpretedEUFConjunction:
		if negated {
			return false
		}
		for _, relation := range value.values() {
			if !problem.boolean(relation, false) {
				return false
			}
		}
		return true
	case BitVectorEUFRelation:
		left, leftOK := problem.compactBitVectorTerm(value.Left)
		right, rightOK := problem.compactBitVectorTerm(value.Right)
		if !leftOK || !rightOK || problem.nodes[left].sortID != problem.nodes[right].sortID {
			return false
		}
		pair := eufPair{left: left, right: right}
		if value.Negated != negated {
			problem.disequality = append(problem.disequality, pair)
		} else {
			problem.equalities = append(problem.equalities, pair)
		}
		return true
	case BitVectorEUFConjunction:
		if negated {
			return false
		}
		for _, relation := range value.values() {
			if !problem.boolean(relation, false) {
				return false
			}
		}
		return true
	default:
		return false
	}
}

func (problem *eufProblem) term(term any) (int, bool) {
	var node eufNode
	switch value := term.(type) {
	case uninterpretedValue[UninterpretedSort]:
		node = eufNode{sortID: value.sortID, symbolID: value.iD}
	case RealSymbol:
		node = eufNode{sortID: -1, symbolID: value.ID}
	case bitVectorSymbol[BitVecSort]:
		node = eufNode{sortID: bitVectorEUFSort(value.width), symbolID: value.iD}
	case unaryApplication[UninterpretedSort]:
		function, ok := value.function.(unaryFunctionValue)
		if !ok {
			return 0, false
		}
		argument, ok := problem.term(value.argument)
		if !ok || problem.nodes[argument].sortID != function.domainID {
			return 0, false
		}
		node = eufNode{kind: 1, sortID: function.rangeID, functionID: function.iD, firstSortID: function.domainID, first: argument, second: -1}
	case binaryApplication[UninterpretedSort]:
		function, ok := value.function.(binaryFunctionValue)
		if !ok {
			return 0, false
		}
		first, firstOK := problem.term(value.first)
		second, secondOK := problem.term(value.second)
		if !firstOK || !secondOK || problem.nodes[first].sortID != function.firstID || problem.nodes[second].sortID != function.secondID {
			return 0, false
		}
		node = eufNode{kind: 2, sortID: function.rangeID, functionID: function.iD, firstSortID: function.firstID, secondSortID: function.secondID, first: first, second: second}
	case sortedUnaryApplication[RealSort]:
		function, ok := value.function.(sortedUnaryFunctionValue[RealSort, RealSort])
		if !ok || value.rangeKind != -1 {
			return 0, false
		}
		argument, ok := problem.term(value.argument)
		if !ok || problem.nodes[argument].sortID != function.domainKind {
			return 0, false
		}
		node = eufNode{kind: 1, sortID: function.rangeKind, functionID: function.iD, firstSortID: function.domainKind, first: argument, second: -1}
	case sortedBinaryApplication[RealSort]:
		function, ok := value.function.(sortedBinaryFunctionValue[RealSort, RealSort, RealSort])
		if !ok || value.rangeKind != -1 {
			return 0, false
		}
		first, firstOK := problem.term(value.first)
		second, secondOK := problem.term(value.second)
		if !firstOK || !secondOK || problem.nodes[first].sortID != function.firstKind || problem.nodes[second].sortID != function.secondKind {
			return 0, false
		}
		node = eufNode{kind: 2, sortID: function.rangeKind, functionID: function.iD, firstSortID: function.firstKind, secondSortID: function.secondKind, first: first, second: second}
	case sortedUnaryApplication[BitVecSort]:
		function, ok := value.function.(sortedUnaryFunctionValue[BitVecSort, BitVecSort])
		if !ok || value.rangeKind != 0 {
			return 0, false
		}
		argument, ok := problem.term(value.argument)
		domainSort := bitVectorEUFSort(function.domainKind)
		if !ok || problem.nodes[argument].sortID != domainSort {
			return 0, false
		}
		node = eufNode{kind: 1, sortID: bitVectorEUFSort(function.rangeKind), functionID: function.iD, firstSortID: domainSort, first: argument, second: -1}
	case sortedBinaryApplication[BitVecSort]:
		function, ok := value.function.(sortedBinaryFunctionValue[BitVecSort, BitVecSort, BitVecSort])
		if !ok || value.rangeKind != 0 {
			return 0, false
		}
		first, firstOK := problem.term(value.first)
		second, secondOK := problem.term(value.second)
		firstSort, secondSort := bitVectorEUFSort(function.firstKind), bitVectorEUFSort(function.secondKind)
		if !firstOK || !secondOK || problem.nodes[first].sortID != firstSort || problem.nodes[second].sortID != secondSort {
			return 0, false
		}
		node = eufNode{kind: 2, sortID: bitVectorEUFSort(function.rangeKind), functionID: function.iD, firstSortID: firstSort, secondSortID: secondSort, first: first, second: second}
	default:
		return 0, false
	}
	return problem.ensureNode(node), true
}

func bitVectorEUFSort(width int) int { return -1000000 - width }

func (problem *eufProblem) realUnaryApplication(functionID, argumentID int) int {
	argument := problem.ensureNode(eufNode{sortID: -1, symbolID: argumentID})
	return problem.ensureNode(eufNode{kind: 1, sortID: -1, functionID: functionID, firstSortID: -1, first: argument, second: -1})
}

func (problem *eufProblem) realBinaryApplication(functionID, firstID, secondID int) int {
	first := problem.ensureNode(eufNode{sortID: -1, symbolID: firstID})
	second := problem.ensureNode(eufNode{sortID: -1, symbolID: secondID})
	return problem.ensureNode(eufNode{kind: 2, sortID: -1, functionID: functionID, firstSortID: -1, secondSortID: -1, first: first, second: second})
}

func (problem *eufProblem) ensureNode(node eufNode) int {
	for index, existing := range problem.nodes {
		if existing == node {
			return index
		}
	}
	index := len(problem.nodes)
	problem.nodes = append(problem.nodes, node)
	problem.parents = append(problem.parents, index)
	problem.ranks = append(problem.ranks, 0)
	return index
}

func (problem *eufProblem) find(node int) int {
	root := node
	for problem.parents[root] != root {
		root = problem.parents[root]
	}
	for problem.parents[node] != node {
		parent := problem.parents[node]
		problem.parents[node] = root
		node = parent
	}
	return root
}

func (problem *eufProblem) union(left, right int) {
	left = problem.find(left)
	right = problem.find(right)
	if left == right {
		return
	}
	if problem.ranks[left] < problem.ranks[right] {
		left, right = right, left
	}
	problem.parents[right] = left
	if problem.ranks[left] == problem.ranks[right] {
		problem.ranks[left]++
	}
}
