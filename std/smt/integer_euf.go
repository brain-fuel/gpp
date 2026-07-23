package smt

// Shared integer EUF/LIA uses purification: every Int-sorted function
// application receives a fresh integer symbol, EUF retains the defining
// application equality, and LIA receives the purified affine constraints.
// Equalities move in both directions until neither solver adds information.

type IntegerUnaryComparison struct {
	FunctionID        int
	ArgumentID        int
	Bound             IntegerValue
	ApplicationOnLeft bool
	Strict            bool
}

func (IntegerUnaryComparison) isTerm(BoolSort) {}

type IntegerBinaryComparison struct {
	FunctionID        int
	FirstArgumentID   int
	SecondArgumentID  int
	Bound             IntegerValue
	ApplicationOnLeft bool
	Strict            bool
}

func (IntegerBinaryComparison) isTerm(BoolSort) {}

type IntegerTernaryComparison struct {
	FunctionID        int
	FirstArgumentID   int
	SecondArgumentID  int
	ThirdArgumentID   int
	Bound             IntegerValue
	ApplicationOnLeft bool
	Strict            bool
}

func (IntegerTernaryComparison) isTerm(BoolSort) {}

type CompactIntegerEUFSystem struct {
	EqualityCount              int
	EqualityLeft               [4]int
	EqualityRight              [4]int
	OverflowEqualityLeft       []int
	OverflowEqualityRight      []int
	UnaryComparisonCount       int
	UnaryComparisons           [4]IntegerUnaryComparison
	OverflowUnaryComparisons   []IntegerUnaryComparison
	BinaryComparisonCount      int
	BinaryComparisons          [4]IntegerBinaryComparison
	OverflowBinaryComparisons  []IntegerBinaryComparison
	TernaryComparisonCount     int
	TernaryComparisons         [4]IntegerTernaryComparison
	OverflowTernaryComparisons []IntegerTernaryComparison
	DifferenceCount            int
	Differences                [4]IntegerDifferenceConstraint
	OverflowDifferences        []IntegerDifferenceConstraint
	RelationCount              int
	Relations                  [4]UninterpretedEUFRelation
	OverflowRelations          []UninterpretedEUFRelation
}

func (CompactIntegerEUFSystem) isTerm(BoolSort) {}

func (system CompactIntegerEUFSystem) equalityValues() ([]int, []int) {
	if system.OverflowEqualityLeft != nil {
		return system.OverflowEqualityLeft[:system.EqualityCount],
			system.OverflowEqualityRight[:system.EqualityCount]
	}
	return system.EqualityLeft[:system.EqualityCount],
		system.EqualityRight[:system.EqualityCount]
}

func (system CompactIntegerEUFSystem) unaryValues() []IntegerUnaryComparison {
	if system.OverflowUnaryComparisons != nil {
		return system.OverflowUnaryComparisons[:system.UnaryComparisonCount]
	}
	return system.UnaryComparisons[:system.UnaryComparisonCount]
}

func (system CompactIntegerEUFSystem) binaryValues() []IntegerBinaryComparison {
	if system.OverflowBinaryComparisons != nil {
		return system.OverflowBinaryComparisons[:system.BinaryComparisonCount]
	}
	return system.BinaryComparisons[:system.BinaryComparisonCount]
}

func (system CompactIntegerEUFSystem) ternaryValues() []IntegerTernaryComparison {
	if system.OverflowTernaryComparisons != nil {
		return system.OverflowTernaryComparisons[:system.TernaryComparisonCount]
	}
	return system.TernaryComparisons[:system.TernaryComparisonCount]
}

func (system CompactIntegerEUFSystem) differenceValues() []IntegerDifferenceConstraint {
	if system.OverflowDifferences != nil {
		return system.OverflowDifferences[:system.DifferenceCount]
	}
	return system.Differences[:system.DifferenceCount]
}

func (system CompactIntegerEUFSystem) relationValues() []UninterpretedEUFRelation {
	if system.OverflowRelations != nil {
		return system.OverflowRelations[:system.RelationCount]
	}
	return system.Relations[:system.RelationCount]
}

type compactIntegerEUFClass struct {
	arity    uint8
	function int
	first    int
	second   int
	third    int
	lower    IntegerValue
	upper    IntegerValue
	hasLower bool
	hasUpper bool
}

func solveCompactIntegerEUFSystem(
	system CompactIntegerEUFSystem,
) (checkOutcome, bool) {
	if system.RelationCount != 0 {
		if outcome, decided := solveCompactIntegerEUFCongruence(system); decided {
			return outcome, true
		}
		return expandCompactIntegerEUFSystem(system)
	}
	leftIDs, rightIDs := system.equalityValues()
	var ids [16]int
	var parents [16]int
	count := 0
	node := func(id int) (int, bool) {
		for index := 0; index < count; index++ {
			if ids[index] == id {
				return index, true
			}
		}
		if count == len(ids) {
			return 0, false
		}
		ids[count], parents[count] = id, count
		count++
		return count - 1, true
	}
	var find func(int) int
	find = func(value int) int {
		if parents[value] != value {
			parents[value] = find(parents[value])
		}
		return parents[value]
	}
	union := func(left, right int) {
		left, right = find(left), find(right)
		if left != right {
			parents[right] = left
		}
	}
	for index := range leftIDs {
		left, leftOK := node(leftIDs[index])
		right, rightOK := node(rightIDs[index])
		if !leftOK || !rightOK {
			return checkOutcome{}, false
		}
		union(left, right)
	}
	for _, comparison := range system.unaryValues() {
		if _, ok := node(comparison.ArgumentID); !ok {
			return checkOutcome{}, false
		}
	}
	for _, comparison := range system.binaryValues() {
		if _, ok := node(comparison.FirstArgumentID); !ok {
			return checkOutcome{}, false
		}
		if _, ok := node(comparison.SecondArgumentID); !ok {
			return checkOutcome{}, false
		}
	}
	for _, comparison := range system.ternaryValues() {
		if _, ok := node(comparison.FirstArgumentID); !ok {
			return checkOutcome{}, false
		}
		if _, ok := node(comparison.SecondArgumentID); !ok {
			return checkOutcome{}, false
		}
		if _, ok := node(comparison.ThirdArgumentID); !ok {
			return checkOutcome{}, false
		}
	}
	var classes [8]compactIntegerEUFClass
	classCount := 0
	appendBound := func(
		arity uint8, function, firstID, secondID, thirdID int,
		bound IntegerValue, applicationOnLeft, strict bool,
	) bool {
		first, _ := node(firstID)
		first = find(first)
		second := 0
		third := 0
		if arity == 2 {
			second, _ = node(secondID)
			second = find(second)
		}
		if arity == 3 {
			second, _ = node(secondID)
			second = find(second)
			third, _ = node(thirdID)
			third = find(third)
		}
		class := -1
		for index := 0; index < classCount; index++ {
			value := classes[index]
			if value.arity == arity && value.function == function &&
				value.first == first &&
				(arity == 1 || value.second == second) &&
				(arity != 3 || value.third == third) {
				class = index
				break
			}
		}
		if class < 0 {
			if classCount == len(classes) {
				return false
			}
			class = classCount
			classes[class] = compactIntegerEUFClass{
				arity: arity, function: function, first: first,
				second: second, third: third,
			}
			classCount++
		}
		value := &classes[class]
		if applicationOnLeft {
			if strict {
				bound = AddIntegerValue(bound, NewIntegerValue(-1))
			}
			if !value.hasUpper ||
				CompareIntegerValue(bound, value.upper) < 0 {
				value.upper, value.hasUpper = bound, true
			}
		} else {
			if strict {
				bound = AddIntegerValue(bound, NewIntegerValue(1))
			}
			if !value.hasLower ||
				CompareIntegerValue(bound, value.lower) > 0 {
				value.lower, value.hasLower = bound, true
			}
		}
		return true
	}
	for _, comparison := range system.unaryValues() {
		if !appendBound(
			1, comparison.FunctionID, comparison.ArgumentID, 0, 0,
			comparison.Bound, comparison.ApplicationOnLeft, comparison.Strict,
		) {
			return checkOutcome{}, false
		}
	}
	for _, comparison := range system.binaryValues() {
		if !appendBound(
			2, comparison.FunctionID,
			comparison.FirstArgumentID, comparison.SecondArgumentID, 0,
			comparison.Bound, comparison.ApplicationOnLeft, comparison.Strict,
		) {
			return checkOutcome{}, false
		}
	}
	for _, comparison := range system.ternaryValues() {
		if !appendBound(
			3, comparison.FunctionID,
			comparison.FirstArgumentID, comparison.SecondArgumentID,
			comparison.ThirdArgumentID,
			comparison.Bound, comparison.ApplicationOnLeft, comparison.Strict,
		) {
			return checkOutcome{}, false
		}
	}
	for index := 0; index < classCount; index++ {
		value := classes[index]
		if value.hasLower && value.hasUpper &&
			CompareIntegerValue(value.lower, value.upper) > 0 {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	var model integerModel
	for index := 0; index < count; index++ {
		model.set(ids[index], IntegerValue{})
	}
	return checkOutcome{status: checkSat, integers: model}, true
}

func solveCompactIntegerEUFCongruence(
	system CompactIntegerEUFSystem,
) (checkOutcome, bool) {
	difference := differenceProblem{}
	difference.edges = difference.inlineEdges[:0]
	for _, constraint := range system.differenceValues() {
		if !difference.compactConstraint(constraint) {
			return checkOutcome{}, false
		}
	}
	if difference.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	problem := eufProblem{}
	problem.initialize()
	for _, relation := range system.relationValues() {
		if !problem.boolean(relation, false) {
			return checkOutcome{}, false
		}
	}
	for left := 0; left < len(problem.nodes); left++ {
		leftNode := problem.nodes[left]
		if leftNode.kind != 1 && leftNode.kind != 2 {
			continue
		}
		for right := left + 1; right < len(problem.nodes); right++ {
			rightNode := problem.nodes[right]
			if leftNode.kind != rightNode.kind ||
				leftNode.functionID != rightNode.functionID ||
				leftNode.firstSortID != rightNode.firstSortID ||
				leftNode.secondSortID != rightNode.secondSortID {
				continue
			}
			firstLeft, firstLeftOK := integerEUFSymbolID(&problem, leftNode.first)
			firstRight, firstRightOK := integerEUFSymbolID(&problem, rightNode.first)
			if firstLeftOK && firstRightOK {
				firstLeftNode := difference.node(firstLeft)
				firstRightNode := difference.node(firstRight)
				if difference.pathAtMost(firstLeftNode, firstRightNode, IntegerValue{}) &&
					difference.pathAtMost(firstRightNode, firstLeftNode, IntegerValue{}) {
					problem.union(leftNode.first, rightNode.first)
				}
			}
			if leftNode.kind == 2 {
				secondLeft, secondLeftOK := integerEUFSymbolID(&problem, leftNode.second)
				secondRight, secondRightOK := integerEUFSymbolID(&problem, rightNode.second)
				if secondLeftOK && secondRightOK {
					secondLeftNode := difference.node(secondLeft)
					secondRightNode := difference.node(secondRight)
					if difference.pathAtMost(secondLeftNode, secondRightNode, IntegerValue{}) &&
						difference.pathAtMost(secondRightNode, secondLeftNode, IntegerValue{}) {
						problem.union(leftNode.second, rightNode.second)
					}
				}
			}
		}
	}
	outcome, recognized := problem.solve()
	if recognized && outcome.status == checkUnsat {
		return outcome, true
	}
	return checkOutcome{}, false
}

func expandCompactIntegerEUFSystem(
	system CompactIntegerEUFSystem,
) (checkOutcome, bool) {
	count := system.DifferenceCount + system.RelationCount
	terms := make([]Term[BoolSort], 0, count)
	for _, constraint := range system.differenceValues() {
		terms = append(terms, constraint)
	}
	for _, relation := range system.relationValues() {
		terms = append(terms, relation)
	}
	return solveSharedIntegerEUF(terms)
}

func containsSharedIntegerEUF(term Term[BoolSort]) bool {
	return containsSortedIntegerApplicationBool(term) ||
		containsCompactIntegerEUF(term)
}

func containsCompactIntegerEUF(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			if containsCompactIntegerEUF(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsCompactIntegerEUF(item) {
				return true
			}
		}
	case TheoryConjunction:
		items, _ := value.atomValues()
		for _, item := range items {
			if containsCompactIntegerEUF(item) {
				return true
			}
		}
	case Not:
		return containsCompactIntegerEUF(value.Value)
	case UninterpretedEUFRelation:
		return value.Left.SortID == -2 || value.Right.SortID == -2
	case UninterpretedEUFConjunction:
		for _, relation := range value.values() {
			if relation.Left.SortID == -2 || relation.Right.SortID == -2 {
				return true
			}
		}
	case IntegerUnaryComparison, IntegerBinaryComparison, IntegerTernaryComparison:
		return true
	}
	return false
}

func containsSortedIntegerApplicationBool(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			if containsSortedIntegerApplicationBool(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsSortedIntegerApplicationBool(item) {
				return true
			}
		}
	case TheoryConjunction:
		items, _ := value.atomValues()
		for _, item := range items {
			if containsSortedIntegerApplicationBool(item) {
				return true
			}
		}
	case Not:
		return containsSortedIntegerApplicationBool(value.Value)
	case Equal:
		left, leftOK := value.Left.(Term[IntSort])
		right, rightOK := value.Right.(Term[IntSort])
		return leftOK && containsSortedIntegerApplication(left) ||
			rightOK && containsSortedIntegerApplication(right)
	case LessEqual:
		return containsSortedIntegerApplication(value.Left) ||
			containsSortedIntegerApplication(value.Right)
	case Less:
		return containsSortedIntegerApplication(value.Left) ||
			containsSortedIntegerApplication(value.Right)
	}
	return false
}

func containsSortedIntegerApplication(term Term[IntSort]) bool {
	switch value := term.(type) {
	case sortedUnaryApplication[IntSort], sortedBinaryApplication[IntSort], sortedTernaryApplication[IntSort]:
		return true
	case Add:
		for _, item := range value.Values {
			if containsSortedIntegerApplication(item) {
				return true
			}
		}
	case Subtract:
		return containsSortedIntegerApplication(value.Left) ||
			containsSortedIntegerApplication(value.Right)
	case IntegerScale:
		return containsSortedIntegerApplication(value.Value)
	case If[IntSort]:
		return containsSortedIntegerApplication(value.Then) ||
			containsSortedIntegerApplication(value.Else)
	}
	return false
}

type sharedIntegerPartition struct {
	euf      theoryTerms
	integers theoryTerms
	unsat    bool
}

type sharedIntegerPurifier struct {
	partition            sharedIntegerPartition
	usedCount            int
	inlineUsed           [16]int
	overflowUsed         map[int]bool
	next                 int
	applicationCount     int
	inlineApplications   [8]purifiedApplication
	overflowApplications []purifiedApplication
}

func solveSharedIntegerEUF(assertions []Term[BoolSort]) (checkOutcome, bool) {
	purifier := sharedIntegerPurifier{}
	for _, assertion := range assertions {
		purifier.collectBooleanSymbols(assertion)
	}
	for _, assertion := range assertions {
		if !purifier.add(assertion, false) {
			return checkOutcome{}, false
		}
	}
	if purifier.partition.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	eufTerms, eufNegated := purifier.partition.euf.values()
	if len(eufTerms) == 0 && purifier.applicationCount == 0 {
		return checkOutcome{}, false
	}
	problem := eufProblem{}
	problem.initialize()
	for index, term := range eufTerms {
		if !problem.boolean(term, eufNegated[index]) {
			return checkOutcome{}, false
		}
	}
	for _, application := range purifier.applicationValues() {
		left := problem.integerUnaryApplication(
			application.functionID, application.firstArgumentID,
		)
		if application.arity == 2 {
			left = problem.integerBinaryApplication(
				application.functionID,
				application.firstArgumentID,
				application.secondArgumentID,
			)
		} else if application.arity == 3 {
			left = problem.integerTernaryApplication(
				application.functionID,
				application.firstArgumentID,
				application.secondArgumentID,
				application.thirdArgumentID,
			)
		}
		right := problem.ensureNode(eufNode{sortID: -2, symbolID: application.resultID})
		problem.equalities = append(problem.equalities, eufPair{left: left, right: right})
	}
	var inlineNodes [24]eufRealNode
	nodes := inlineNodes[:0]
	for node, value := range problem.nodes {
		if value.kind == 0 && value.sortID == -2 {
			nodes = append(nodes, eufRealNode{id: value.symbolID, node: node})
		}
	}
	var inlineExchanged [24]eufPair
	exchanged := inlineExchanged[:0]
	for {
		integerTerms, _ := purifier.partition.integers.values()
		exchangeIntegerApplicationArguments(&problem, integerTerms)
		eufOutcome, recognized := problem.solve()
		if !recognized {
			return checkOutcome{}, false
		}
		if eufOutcome.status == checkUnsat {
			return eufOutcome, true
		}
		added := false
		for left := 0; left < len(nodes); left++ {
			for right := left + 1; right < len(nodes); right++ {
				if problem.find(nodes[left].node) != problem.find(nodes[right].node) ||
					containsEUFPair(exchanged, nodes[left].id, nodes[right].id) {
					continue
				}
				exchanged = append(exchanged, eufPair{
					left: nodes[left].id, right: nodes[right].id,
				})
				purifier.partition.integers.append(Equal{
					Left:  IntSymbol{ID: nodes[left].id},
					Right: IntSymbol{ID: nodes[right].id},
				}, false)
				added = true
			}
		}
		integerTerms, _ = purifier.partition.integers.values()
		integerOutcome, recognized := solveIntegerConjunction(integerTerms)
		if !recognized {
			return checkOutcome{}, false
		}
		if integerOutcome.status == checkUnsat {
			return integerOutcome, true
		}
		if added {
			continue
		}
		entailed := exchangeIntegerApplicationArguments(&problem, integerTerms)
		if !entailed {
			return integerOutcome, true
		}
	}
}

func exchangeIntegerApplicationArguments(
	problem *eufProblem, assertions []Term[BoolSort],
) bool {
	oracle := newIntegerEqualityOracle(assertions)
	changed := false
	for left := 0; left < len(problem.nodes); left++ {
		leftNode := problem.nodes[left]
		if leftNode.kind != 1 && leftNode.kind != 2 && leftNode.kind != 4 {
			continue
		}
		for right := left + 1; right < len(problem.nodes); right++ {
			rightNode := problem.nodes[right]
			if rightNode.kind != leftNode.kind ||
				rightNode.functionID != leftNode.functionID ||
				rightNode.firstSortID != leftNode.firstSortID ||
				rightNode.secondSortID != leftNode.secondSortID ||
				rightNode.thirdSortID != leftNode.thirdSortID ||
				rightNode.sortID != leftNode.sortID {
				continue
			}
			if problem.find(leftNode.first) != problem.find(rightNode.first) {
				leftID, leftOK := integerEUFSymbolID(problem, leftNode.first)
				rightID, rightOK := integerEUFSymbolID(problem, rightNode.first)
				if leftOK && rightOK && oracle.entails(leftID, rightID) {
					problem.union(leftNode.first, rightNode.first)
					changed = true
				}
			}
			if (leftNode.kind == 2 || leftNode.kind == 4) &&
				problem.find(leftNode.second) != problem.find(rightNode.second) {
				leftID, leftOK := integerEUFSymbolID(problem, leftNode.second)
				rightID, rightOK := integerEUFSymbolID(problem, rightNode.second)
				if leftOK && rightOK && oracle.entails(leftID, rightID) {
					problem.union(leftNode.second, rightNode.second)
					changed = true
				}
			}
			if leftNode.kind == 4 &&
				problem.find(leftNode.third) != problem.find(rightNode.third) {
				leftID, leftOK := integerEUFSymbolID(problem, leftNode.third)
				rightID, rightOK := integerEUFSymbolID(problem, rightNode.third)
				if leftOK && rightOK && oracle.entails(leftID, rightID) {
					problem.union(leftNode.third, rightNode.third)
					changed = true
				}
			}
		}
	}
	return changed
}

func integerEUFSymbolID(problem *eufProblem, node int) (int, bool) {
	value := problem.nodes[node]
	return value.symbolID, value.kind == 0 && value.sortID == -2
}

type integerEqualityOracle struct {
	assertions   []Term[BoolSort]
	difference   differenceProblem
	differenceOK bool
}

func newIntegerEqualityOracle(
	assertions []Term[BoolSort],
) integerEqualityOracle {
	oracle := integerEqualityOracle{assertions: assertions}
	oracle.difference.edges = oracle.difference.inlineEdges[:0]
	oracle.differenceOK = true
	for _, assertion := range assertions {
		if !oracle.difference.boolean(assertion) {
			oracle.differenceOK = false
			break
		}
	}
	return oracle
}

func (oracle *integerEqualityOracle) entails(leftID, rightID int) bool {
	if leftID == rightID {
		return true
	}
	if oracle.differenceOK {
		left := oracle.difference.node(leftID)
		right := oracle.difference.node(rightID)
		return oracle.difference.pathAtMost(left, right, IntegerValue{}) &&
			oracle.difference.pathAtMost(right, left, IntegerValue{})
	}
	return integerEntailsSymbolEquality(oracle.assertions, leftID, rightID)
}

func (purifier *sharedIntegerPurifier) appendApplicationBound(
	result IntSymbol, bound IntegerValue, applicationOnLeft, strict bool,
) {
	constant := IntegerTerm(bound)
	left, right := Term[IntSort](result), constant
	if !applicationOnLeft {
		left, right = right, left
	}
	if strict {
		purifier.partition.integers.append(Less{Left: left, Right: right}, false)
		return
	}
	purifier.partition.integers.append(
		LessEqual{Left: left, Right: right}, false,
	)
}

func (problem *eufProblem) integerUnaryApplication(functionID, argumentID int) int {
	argument := problem.ensureNode(eufNode{sortID: -2, symbolID: argumentID})
	return problem.ensureNode(eufNode{
		kind: 1, sortID: -2, functionID: functionID,
		firstSortID: -2, first: argument, second: -1,
	})
}

func (problem *eufProblem) integerBinaryApplication(
	functionID, firstID, secondID int,
) int {
	first := problem.ensureNode(eufNode{sortID: -2, symbolID: firstID})
	second := problem.ensureNode(eufNode{sortID: -2, symbolID: secondID})
	return problem.ensureNode(eufNode{
		kind: 2, sortID: -2, functionID: functionID,
		firstSortID: -2, secondSortID: -2, first: first, second: second,
	})
}

func (problem *eufProblem) integerTernaryApplication(
	functionID, firstID, secondID, thirdID int,
) int {
	first := problem.ensureNode(eufNode{sortID: -2, symbolID: firstID})
	second := problem.ensureNode(eufNode{sortID: -2, symbolID: secondID})
	third := problem.ensureNode(eufNode{sortID: -2, symbolID: thirdID})
	return problem.ensureNode(eufNode{
		kind: 4, sortID: -2, functionID: functionID,
		firstSortID: -2, secondSortID: -2, thirdSortID: -2,
		first: first, second: second, third: third,
	})
}

func (purifier *sharedIntegerPurifier) add(term Term[BoolSort], negated bool) bool {
	switch value := term.(type) {
	case Bool:
		purifier.partition.unsat = purifier.partition.unsat || value.Value == negated
		return true
	case And:
		if negated {
			return false
		}
		for _, item := range value.Values {
			if !purifier.add(item, false) {
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
			if !purifier.add(item, polarities[index]) {
				return false
			}
		}
		return true
	case TheoryConjunction:
		if negated || value.RealCount != 0 ||
			value.SymbolEqualityCount != 0 ||
			value.UnaryComparisonCount != 0 ||
			value.BinaryComparisonCount != 0 {
			return false
		}
		items, polarities := value.atomValues()
		for index, item := range items {
			if !purifier.add(item, polarities[index]) {
				return false
			}
		}
		return true
	case Not:
		return purifier.add(value.Value, !negated)
	case LessEqual:
		if negated {
			return false
		}
		left, leftOK := purifier.integer(value.Left)
		right, rightOK := purifier.integer(value.Right)
		if !leftOK || !rightOK {
			return false
		}
		purifier.partition.integers.append(
			LessEqual{Left: left, Right: right}, false,
		)
		return true
	case Less:
		if negated {
			return false
		}
		left, leftOK := purifier.integer(value.Left)
		right, rightOK := purifier.integer(value.Right)
		if !leftOK || !rightOK {
			return false
		}
		purifier.partition.integers.append(Less{Left: left, Right: right}, false)
		return true
	case Equal:
		left, leftOK := value.Left.(Term[IntSort])
		right, rightOK := value.Right.(Term[IntSort])
		if !leftOK || !rightOK {
			return purifier.partitionTerm(term, negated)
		}
		purifiedLeft, leftOK := purifier.integer(left)
		purifiedRight, rightOK := purifier.integer(right)
		if !leftOK || !rightOK {
			return false
		}
		equality := Equal{Left: purifiedLeft, Right: purifiedRight}
		if negated {
			purifier.partition.euf.append(equality, true)
		} else {
			purifier.partition.integers.append(equality, false)
		}
		return true
	case IntegerUnaryComparison:
		if negated {
			return false
		}
		result := purifier.unaryApplication(value.FunctionID, value.ArgumentID)
		purifier.appendApplicationBound(
			result, value.Bound, value.ApplicationOnLeft, value.Strict,
		)
		return true
	case IntegerBinaryComparison:
		if negated {
			return false
		}
		result := purifier.binaryApplication(
			value.FunctionID, value.FirstArgumentID, value.SecondArgumentID,
		)
		purifier.appendApplicationBound(
			result, value.Bound, value.ApplicationOnLeft, value.Strict,
		)
		return true
	case IntegerTernaryComparison:
		if negated {
			return false
		}
		result := purifier.ternaryApplication(
			value.FunctionID, value.FirstArgumentID,
			value.SecondArgumentID, value.ThirdArgumentID,
		)
		purifier.appendApplicationBound(
			result, value.Bound, value.ApplicationOnLeft, value.Strict,
		)
		return true
	}
	return purifier.partitionTerm(term, negated)
}

func (purifier *sharedIntegerPurifier) partitionTerm(
	term Term[BoolSort], negated bool,
) bool {
	if containsEUF(term) {
		purifier.partition.euf.append(term, negated)
		return true
	}
	if containsIntegerTheory(term) && !negated {
		purifier.partition.integers.append(term, false)
		return true
	}
	return false
}

func (purifier *sharedIntegerPurifier) integer(
	term Term[IntSort],
) (Term[IntSort], bool) {
	switch value := term.(type) {
	case Integer, integerExact[IntSort], IntSymbol, integerVariable[IntSort]:
		return term, true
	case Add:
		items := make([]Term[IntSort], len(value.Values))
		for index, item := range value.Values {
			purified, ok := purifier.integer(item)
			if !ok {
				return nil, false
			}
			items[index] = purified
		}
		return Add{Values: items}, true
	case Subtract:
		left, leftOK := purifier.integer(value.Left)
		right, rightOK := purifier.integer(value.Right)
		return Subtract{Left: left, Right: right}, leftOK && rightOK
	case IntegerScale:
		item, ok := purifier.integer(value.Value)
		return IntegerScale{Coefficient: value.Coefficient, Value: item}, ok
	case sortedUnaryApplication[IntSort]:
		function, ok := value.function.(sortedUnaryFunctionValue[IntSort, IntSort])
		argument, argumentOK := value.argument.(Term[IntSort])
		if !ok || !argumentOK || value.rangeKind != -1 {
			return nil, false
		}
		argumentSymbol, ok := purifier.integerArgument(argument)
		if !ok {
			return nil, false
		}
		return purifier.unaryApplication(function.iD, argumentSymbol.ID), true
	case sortedBinaryApplication[IntSort]:
		function, ok := value.function.(sortedBinaryFunctionValue[IntSort, IntSort, IntSort])
		first, firstOK := value.first.(Term[IntSort])
		second, secondOK := value.second.(Term[IntSort])
		if !ok || !firstOK || !secondOK || value.rangeKind != -1 {
			return nil, false
		}
		firstSymbol, firstOK := purifier.integerArgument(first)
		secondSymbol, secondOK := purifier.integerArgument(second)
		if !firstOK || !secondOK {
			return nil, false
		}
		return purifier.binaryApplication(
			function.iD, firstSymbol.ID, secondSymbol.ID,
		), true
	case sortedTernaryApplication[IntSort]:
		function, ok := value.function.(sortedTernaryFunctionValue[IntSort, IntSort, IntSort, IntSort])
		first, firstOK := value.first.(Term[IntSort])
		second, secondOK := value.second.(Term[IntSort])
		third, thirdOK := value.third.(Term[IntSort])
		if !ok || !firstOK || !secondOK || !thirdOK || value.rangeKind != -1 {
			return nil, false
		}
		firstSymbol, firstOK := purifier.integerArgument(first)
		secondSymbol, secondOK := purifier.integerArgument(second)
		thirdSymbol, thirdOK := purifier.integerArgument(third)
		if !firstOK || !secondOK || !thirdOK {
			return nil, false
		}
		return purifier.ternaryApplication(
			function.iD, firstSymbol.ID, secondSymbol.ID, thirdSymbol.ID,
		), true
	}
	return nil, false
}

func (purifier *sharedIntegerPurifier) integerArgument(
	argument Term[IntSort],
) (IntSymbol, bool) {
	purified, ok := purifier.integer(argument)
	if !ok {
		return IntSymbol{}, false
	}
	if id, _, direct := IntegerSymbol(purified); direct {
		return IntSymbol{ID: id}, true
	}
	symbol := IntSymbol{ID: purifier.fresh()}
	purifier.partition.integers.append(
		Equal{Left: symbol, Right: purified}, false,
	)
	return symbol, true
}

func (purifier *sharedIntegerPurifier) unaryApplication(
	functionID, argumentID int,
) IntSymbol {
	return purifier.application(1, functionID, argumentID, 0)
}

func (purifier *sharedIntegerPurifier) binaryApplication(
	functionID, firstArgumentID, secondArgumentID int,
) IntSymbol {
	return purifier.application(
		2, functionID, firstArgumentID, secondArgumentID,
	)
}

func (purifier *sharedIntegerPurifier) ternaryApplication(
	functionID, firstArgumentID, secondArgumentID, thirdArgumentID int,
) IntSymbol {
	return purifier.application(
		3, functionID, firstArgumentID, secondArgumentID, thirdArgumentID,
	)
}

func (purifier *sharedIntegerPurifier) application(
	arity uint8, functionID, firstArgumentID, secondArgumentID int,
	thirdArgumentIDs ...int,
) IntSymbol {
	thirdArgumentID := 0
	if len(thirdArgumentIDs) != 0 {
		thirdArgumentID = thirdArgumentIDs[0]
	}
	for _, application := range purifier.applicationValues() {
		if application.arity == arity &&
			application.functionID == functionID &&
			application.firstArgumentID == firstArgumentID &&
			application.secondArgumentID == secondArgumentID &&
			application.thirdArgumentID == thirdArgumentID {
			return IntSymbol{ID: application.resultID}
		}
	}
	result := IntSymbol{ID: purifier.fresh()}
	purifier.appendApplication(purifiedApplication{
		arity: arity, functionID: functionID,
		firstArgumentID:  firstArgumentID,
		secondArgumentID: secondArgumentID,
		thirdArgumentID:  thirdArgumentID,
		resultID:         result.ID,
	})
	return result
}

func (purifier *sharedIntegerPurifier) applicationValues() []purifiedApplication {
	if purifier.overflowApplications != nil {
		return purifier.overflowApplications[:purifier.applicationCount]
	}
	return purifier.inlineApplications[:purifier.applicationCount]
}

func (purifier *sharedIntegerPurifier) appendApplication(
	value purifiedApplication,
) {
	if purifier.applicationCount < len(purifier.inlineApplications) &&
		purifier.overflowApplications == nil {
		purifier.inlineApplications[purifier.applicationCount] = value
		purifier.applicationCount++
		return
	}
	if purifier.overflowApplications == nil {
		purifier.overflowApplications = make(
			[]purifiedApplication,
			purifier.applicationCount,
			purifier.applicationCount*2,
		)
		copy(
			purifier.overflowApplications,
			purifier.inlineApplications[:purifier.applicationCount],
		)
	}
	purifier.overflowApplications = append(purifier.overflowApplications, value)
	purifier.applicationCount++
}

func (purifier *sharedIntegerPurifier) collectBooleanSymbols(
	term Term[BoolSort],
) {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			purifier.collectBooleanSymbols(item)
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			purifier.collectBooleanSymbols(item)
		}
	case TheoryConjunction:
		items, _ := value.atomValues()
		for _, item := range items {
			purifier.collectBooleanSymbols(item)
		}
	case Not:
		purifier.collectBooleanSymbols(value.Value)
	case LessEqual:
		purifier.collectIntegerSymbols(value.Left)
		purifier.collectIntegerSymbols(value.Right)
	case Less:
		purifier.collectIntegerSymbols(value.Left)
		purifier.collectIntegerSymbols(value.Right)
	case Equal:
		if left, ok := value.Left.(Term[IntSort]); ok {
			purifier.collectIntegerSymbols(left)
		}
		if right, ok := value.Right.(Term[IntSort]); ok {
			purifier.collectIntegerSymbols(right)
		}
	case IntegerUnaryComparison:
		purifier.markUsed(value.ArgumentID)
	case IntegerBinaryComparison:
		purifier.markUsed(value.FirstArgumentID)
		purifier.markUsed(value.SecondArgumentID)
	case IntegerTernaryComparison:
		purifier.markUsed(value.FirstArgumentID)
		purifier.markUsed(value.SecondArgumentID)
		purifier.markUsed(value.ThirdArgumentID)
	case UninterpretedEUFRelation:
		purifier.collectCompactIntegerEUFTerm(value.Left)
		purifier.collectCompactIntegerEUFTerm(value.Right)
	}
}

func (purifier *sharedIntegerPurifier) collectCompactIntegerEUFTerm(
	value UninterpretedEUFTerm,
) {
	if value.SortID != -2 {
		return
	}
	switch value.Kind {
	case 1:
		purifier.markUsed(value.SymbolID)
	case 2:
		purifier.markUsed(value.FirstID)
	case 3:
		purifier.markUsed(value.FirstID)
		purifier.markUsed(value.SecondID)
	}
}

func (purifier *sharedIntegerPurifier) collectIntegerSymbols(
	term Term[IntSort],
) {
	switch value := term.(type) {
	case IntSymbol:
		purifier.markUsed(value.ID)
	case integerVariable[IntSort]:
		purifier.markUsed(value.iD)
	case Add:
		for _, item := range value.Values {
			purifier.collectIntegerSymbols(item)
		}
	case Subtract:
		purifier.collectIntegerSymbols(value.Left)
		purifier.collectIntegerSymbols(value.Right)
	case IntegerScale:
		purifier.collectIntegerSymbols(value.Value)
	case sortedUnaryApplication[IntSort]:
		if argument, ok := value.argument.(Term[IntSort]); ok {
			purifier.collectIntegerSymbols(argument)
		}
	case sortedBinaryApplication[IntSort]:
		if first, ok := value.first.(Term[IntSort]); ok {
			purifier.collectIntegerSymbols(first)
		}
		if second, ok := value.second.(Term[IntSort]); ok {
			purifier.collectIntegerSymbols(second)
		}
	case sortedTernaryApplication[IntSort]:
		if first, ok := value.first.(Term[IntSort]); ok {
			purifier.collectIntegerSymbols(first)
		}
		if second, ok := value.second.(Term[IntSort]); ok {
			purifier.collectIntegerSymbols(second)
		}
		if third, ok := value.third.(Term[IntSort]); ok {
			purifier.collectIntegerSymbols(third)
		}
	}
}

func (purifier *sharedIntegerPurifier) fresh() int {
	for purifier.isUsed(purifier.next) {
		purifier.next++
	}
	result := purifier.next
	purifier.markUsed(result)
	purifier.next++
	return result
}

func (purifier *sharedIntegerPurifier) isUsed(id int) bool {
	for index := 0; index < purifier.usedCount &&
		index < len(purifier.inlineUsed); index++ {
		if purifier.inlineUsed[index] == id {
			return true
		}
	}
	return purifier.overflowUsed[id]
}

func (purifier *sharedIntegerPurifier) markUsed(id int) {
	if purifier.isUsed(id) {
		return
	}
	if purifier.usedCount < len(purifier.inlineUsed) {
		purifier.inlineUsed[purifier.usedCount] = id
		purifier.usedCount++
		return
	}
	if purifier.overflowUsed == nil {
		purifier.overflowUsed = make(map[int]bool)
	}
	purifier.overflowUsed[id] = true
	purifier.usedCount++
}

func solveIntegerConjunction(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if containsGeneralLinearIntegerAssertions(assertions) {
		if outcome, recognized := solveLinearIntegerAssertions(assertions); recognized {
			return outcome, true
		}
	}
	if outcome, recognized := solveDifferenceAssertions(assertions); recognized {
		return outcome, true
	}
	if outcome, recognized := solveLinearIntegerAssertions(assertions); recognized {
		return outcome, true
	}
	return checkOutcome{}, false
}

func integerEntailsSymbolEquality(
	assertions []Term[BoolSort], leftID, rightID int,
) bool {
	if leftID == rightID {
		return true
	}
	if entailed, recognized := differenceEntailsEquality(
		assertions, leftID, rightID,
	); recognized {
		return entailed
	}
	left := IntSymbol{ID: leftID}
	right := IntSymbol{ID: rightID}
	return integerUnsatWith(
		assertions, Less{Left: left, Right: right},
	) && integerUnsatWith(
		assertions, Less{Left: right, Right: left},
	)
}

func integerUnsatWith(
	assertions []Term[BoolSort], extra Term[BoolSort],
) bool {
	if len(assertions)+1 <= 24 {
		var inline [24]Term[BoolSort]
		copy(inline[:], assertions)
		inline[len(assertions)] = extra
		outcome, recognized := solveIntegerConjunction(
			inline[:len(assertions)+1],
		)
		return recognized && outcome.status == checkUnsat
	}
	combined := make([]Term[BoolSort], len(assertions)+1)
	copy(combined, assertions)
	combined[len(assertions)] = extra
	outcome, recognized := solveIntegerConjunction(combined)
	return recognized && outcome.status == checkUnsat
}
