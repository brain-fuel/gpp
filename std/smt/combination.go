package smt

// TheoryConjunction is a compact mixed conjunction produced after a
// compatibility layer has already normalized affine real constraints while
// retaining other Boolean atoms and their polarity.
type TheoryConjunction struct {
	AtomCount                 int
	Atoms                     [4]Term[BoolSort]
	AtomNegated               [4]bool
	OverflowAtoms             []Term[BoolSort]
	OverflowNegated           []bool
	RealCount                 int
	Reals                     [4]LinearRealConstraint
	OverflowReals             []LinearRealConstraint
	SymbolEqualityCount       int
	SymbolEqualities          [4]RealSymbolEquality
	OverflowSymbolEqualities  []RealSymbolEquality
	UnaryComparisonCount      int
	UnaryComparisons          [4]RealUnaryComparison
	OverflowUnaryComparisons  []RealUnaryComparison
	BinaryComparisonCount     int
	BinaryComparisons         [4]RealBinaryComparison
	OverflowBinaryComparisons []RealBinaryComparison
}

func (conjunction TheoryConjunction) symbolEqualityValues() []RealSymbolEquality {
	if conjunction.OverflowSymbolEqualities != nil {
		return conjunction.OverflowSymbolEqualities[:conjunction.SymbolEqualityCount]
	}
	return conjunction.SymbolEqualities[:conjunction.SymbolEqualityCount]
}

func (conjunction TheoryConjunction) unaryComparisonValues() []RealUnaryComparison {
	if conjunction.OverflowUnaryComparisons != nil {
		return conjunction.OverflowUnaryComparisons[:conjunction.UnaryComparisonCount]
	}
	return conjunction.UnaryComparisons[:conjunction.UnaryComparisonCount]
}

func (conjunction TheoryConjunction) binaryComparisonValues() []RealBinaryComparison {
	if conjunction.OverflowBinaryComparisons != nil {
		return conjunction.OverflowBinaryComparisons[:conjunction.BinaryComparisonCount]
	}
	return conjunction.BinaryComparisons[:conjunction.BinaryComparisonCount]
}

func (TheoryConjunction) isTerm(BoolSort) {}

func (conjunction TheoryConjunction) atomValues() ([]Term[BoolSort], []bool) {
	if conjunction.OverflowAtoms != nil {
		return conjunction.OverflowAtoms[:conjunction.AtomCount], conjunction.OverflowNegated[:conjunction.AtomCount]
	}
	return conjunction.Atoms[:conjunction.AtomCount], conjunction.AtomNegated[:conjunction.AtomCount]
}

func (conjunction TheoryConjunction) realValues() []LinearRealConstraint {
	if conjunction.OverflowReals != nil {
		return conjunction.OverflowReals[:conjunction.RealCount]
	}
	return conjunction.Reals[:conjunction.RealCount]
}

func containsSharedRealEUF(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			if containsSharedRealEUF(item) {
				return true
			}
		}
		return false
	case BooleanConjunction:
		terms, _ := value.values()
		for _, item := range terms {
			if containsSharedRealEUF(item) {
				return true
			}
		}
		return false
	case TheoryConjunction:
		if value.UnaryComparisonCount != 0 || value.BinaryComparisonCount != 0 {
			return true
		}
		terms, _ := value.atomValues()
		for _, item := range terms {
			if containsSharedRealEUF(item) {
				return true
			}
		}
		return false
	case Not:
		return containsSharedRealEUF(value.Value)
	default:
		return containsSortedRealApplicationBool(term) || containsEUF(term) && containsRealTheory(term)
	}
}

func containsSortedRealApplicationBool(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case RealLessEqual:
		return containsSortedRealApplication(value.Left) || containsSortedRealApplication(value.Right)
	case RealLess:
		return containsSortedRealApplication(value.Left) || containsSortedRealApplication(value.Right)
	case Equal:
		left, leftOK := value.Left.(Term[RealSort])
		right, rightOK := value.Right.(Term[RealSort])
		return leftOK && containsSortedRealApplication(left) || rightOK && containsSortedRealApplication(right)
	}
	return false
}

func containsSortedRealApplication(term Term[RealSort]) bool {
	switch value := term.(type) {
	case sortedUnaryApplication[RealSort]:
		return true
	case sortedBinaryApplication[RealSort]:
		return true
	case RealAdd:
		for _, item := range value.Values {
			if containsSortedRealApplication(item) {
				return true
			}
		}
	case RealSubtract:
		return containsSortedRealApplication(value.Left) || containsSortedRealApplication(value.Right)
	case RealScale:
		return containsSortedRealApplication(value.Value)
	case If[RealSort]:
		return containsSortedRealApplication(value.Then) || containsSortedRealApplication(value.Else)
	}
	return false
}

// solveSharedRealEUF performs equality exchange for the convex combination of
// ground EUF and exact linear real arithmetic. Applications are confined to
// EUF atoms; shared RealSymbol nodes are the Nelson--Oppen interface.
func solveSharedRealEUF(assertions []Term[BoolSort]) (checkOutcome, bool) {
	purifier := sharedRealPurifier{}
	partition := &purifier.partition
	for _, assertion := range assertions {
		purifier.collectBooleanSymbols(assertion)
	}
	for _, assertion := range assertions {
		if !purifier.add(assertion, false) {
			return checkOutcome{}, false
		}
	}
	if partition.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	eufTerms, eufNegated := partition.euf.values()
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
		left := problem.realUnaryApplication(application.functionID, application.firstArgumentID)
		if application.arity == 2 {
			left = problem.realBinaryApplication(application.functionID, application.firstArgumentID, application.secondArgumentID)
		}
		right := problem.ensureNode(eufNode{sortID: -1, symbolID: application.resultID})
		problem.equalities = append(problem.equalities, eufPair{left: left, right: right})
	}
	var inlineRealNodes [16]eufRealNode
	realNodes := inlineRealNodes[:0]
	for node, value := range problem.nodes {
		if value.kind == 0 && value.sortID == -1 {
			realNodes = append(realNodes, eufRealNode{id: value.symbolID, node: node})
		}
	}
	realTerms, _ := partition.reals.values()
	var inlineExchanged [16]eufPair
	exchanged := inlineExchanged[:0]
	for {
		for left := 0; left < len(realNodes); left++ {
			for right := left + 1; right < len(realNodes); right++ {
				if linearRealDirectSymbolEquality(realTerms, partition.compactReals.values(), realNodes[left].id, realNodes[right].id) {
					problem.union(realNodes[left].node, realNodes[right].node)
				}
			}
		}
		eufOutcome, recognized := problem.solve()
		if !recognized {
			return checkOutcome{}, false
		}
		if eufOutcome.status == checkUnsat {
			return eufOutcome, true
		}
		added := false
		for left := 0; left < len(realNodes); left++ {
			for right := left + 1; right < len(realNodes); right++ {
				if problem.find(realNodes[left].node) != problem.find(realNodes[right].node) || containsEUFPair(exchanged, realNodes[left].id, realNodes[right].id) {
					continue
				}
				exchanged = append(exchanged, eufPair{left: realNodes[left].id, right: realNodes[right].id})
				partition.reals.append(RealSymbolEquality{LeftID: realNodes[left].id, RightID: realNodes[right].id}, false)
				added = true
			}
		}
		realTerms, _ = partition.reals.values()
		realOutcome, recognized := solveLinearRealParts(realTerms, partition.compactReals.values())
		if !recognized {
			return checkOutcome{}, false
		}
		if realOutcome.status == checkUnsat {
			return realOutcome, true
		}
		if added {
			continue
		}
		entailed := false
		for left := 0; left < len(realNodes); left++ {
			for right := left + 1; right < len(realNodes); right++ {
				if problem.find(realNodes[left].node) == problem.find(realNodes[right].node) {
					continue
				}
				if linearRealEntailsSymbolEquality(realTerms, partition.compactReals.values(), realNodes[left].id, realNodes[right].id) {
					problem.union(realNodes[left].node, realNodes[right].node)
					entailed = true
				}
			}
		}
		if !entailed {
			return realOutcome, true
		}
	}
}

type purifiedApplication struct {
	arity            uint8
	functionID       int
	firstArgumentID  int
	secondArgumentID int
	thirdArgumentID  int
	resultID         int
}

type sharedRealPurifier struct {
	partition            sharedRealPartition
	usedCount            int
	inlineUsed           [16]int
	overflowUsed         map[int]bool
	next                 int
	applicationCount     int
	inlineApplications   [8]purifiedApplication
	overflowApplications []purifiedApplication
}

func (purifier *sharedRealPurifier) fresh() int {
	for purifier.isUsed(purifier.next) {
		purifier.next++
	}
	result := purifier.next
	purifier.markUsed(result)
	purifier.next++
	return result
}

func (purifier *sharedRealPurifier) isUsed(id int) bool {
	for index := 0; index < purifier.usedCount && index < len(purifier.inlineUsed); index++ {
		if purifier.inlineUsed[index] == id {
			return true
		}
	}
	return purifier.overflowUsed[id]
}

func (purifier *sharedRealPurifier) markUsed(id int) {
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

func (purifier *sharedRealPurifier) collectBooleanSymbols(term Term[BoolSort]) {
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
		for _, constraint := range value.realValues() {
			symbols, _ := constraint.coefficientValues()
			for _, id := range symbols {
				purifier.markUsed(id)
			}
		}
		for _, equality := range value.symbolEqualityValues() {
			purifier.markUsed(equality.LeftID)
			purifier.markUsed(equality.RightID)
		}
		for _, comparison := range value.unaryComparisonValues() {
			purifier.markUsed(comparison.ArgumentID)
		}
		for _, comparison := range value.binaryComparisonValues() {
			purifier.markUsed(comparison.FirstArgumentID)
			purifier.markUsed(comparison.SecondArgumentID)
		}
	case Not:
		purifier.collectBooleanSymbols(value.Value)
	case RealLessEqual:
		purifier.collectRealSymbols(value.Left)
		purifier.collectRealSymbols(value.Right)
	case RealLess:
		purifier.collectRealSymbols(value.Left)
		purifier.collectRealSymbols(value.Right)
	case Equal:
		if left, ok := value.Left.(Term[RealSort]); ok {
			purifier.collectRealSymbols(left)
		}
		if right, ok := value.Right.(Term[RealSort]); ok {
			purifier.collectRealSymbols(right)
		}
	case RealUnaryEquality:
		purifier.markUsed(value.LeftArgumentID)
		purifier.markUsed(value.RightArgumentID)
	case RealUnaryComparison:
		purifier.markUsed(value.ArgumentID)
	case RealBinaryComparison:
		purifier.markUsed(value.FirstArgumentID)
		purifier.markUsed(value.SecondArgumentID)
	case RealSymbolEquality:
		purifier.markUsed(value.LeftID)
		purifier.markUsed(value.RightID)
	}
}

func (purifier *sharedRealPurifier) collectRealSymbols(term Term[RealSort]) {
	switch value := term.(type) {
	case RealSymbol:
		purifier.markUsed(value.ID)
	case RealAdd:
		for _, item := range value.Values {
			purifier.collectRealSymbols(item)
		}
	case RealSubtract:
		purifier.collectRealSymbols(value.Left)
		purifier.collectRealSymbols(value.Right)
	case RealScale:
		purifier.collectRealSymbols(value.Value)
	case sortedUnaryApplication[RealSort]:
		if argument, ok := value.argument.(Term[RealSort]); ok {
			purifier.collectRealSymbols(argument)
		}
	case sortedBinaryApplication[RealSort]:
		if first, ok := value.first.(Term[RealSort]); ok {
			purifier.collectRealSymbols(first)
		}
		if second, ok := value.second.(Term[RealSort]); ok {
			purifier.collectRealSymbols(second)
		}
	case If[RealSort]:
		purifier.collectRealSymbols(value.Then)
		purifier.collectRealSymbols(value.Else)
	}
}

func (purifier *sharedRealPurifier) add(term Term[BoolSort], negated bool) bool {
	switch value := term.(type) {
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
		if negated {
			return false
		}
		items, polarities := value.atomValues()
		for index, item := range items {
			if !purifier.add(item, polarities[index]) {
				return false
			}
		}
		for _, constraint := range value.realValues() {
			purifier.partition.compactReals.append(constraint)
		}
		for _, equality := range value.symbolEqualityValues() {
			purifier.partition.appendSymbolEquality(equality)
		}
		for _, comparison := range value.unaryComparisonValues() {
			purifier.appendUnaryComparison(comparison)
		}
		for _, comparison := range value.binaryComparisonValues() {
			purifier.appendBinaryComparison(comparison)
		}
		return true
	case Not:
		return purifier.add(value.Value, !negated)
	case RealLessEqual:
		if negated {
			return false
		}
		left, leftOK := purifier.real(value.Left)
		right, rightOK := purifier.real(value.Right)
		if !leftOK || !rightOK {
			return false
		}
		purifier.partition.reals.append(RealLessEqual{Left: left, Right: right}, false)
		return true
	case RealLess:
		if negated {
			return false
		}
		left, leftOK := purifier.real(value.Left)
		right, rightOK := purifier.real(value.Right)
		if !leftOK || !rightOK {
			return false
		}
		purifier.partition.reals.append(RealLess{Left: left, Right: right}, false)
		return true
	case Equal:
		left, leftOK := value.Left.(Term[RealSort])
		right, rightOK := value.Right.(Term[RealSort])
		if !leftOK || !rightOK || !containsSortedRealApplication(left) && !containsSortedRealApplication(right) {
			return purifier.partition.add(term, negated)
		}
		purifiedLeft, leftOK := purifier.real(left)
		purifiedRight, rightOK := purifier.real(right)
		if !leftOK || !rightOK {
			return false
		}
		if negated {
			leftSymbol, leftOK := purifiedLeft.(RealSymbol)
			rightSymbol, rightOK := purifiedRight.(RealSymbol)
			if !leftOK || !rightOK {
				return false
			}
			purifier.partition.euf.append(Equal{Left: leftSymbol, Right: rightSymbol}, true)
			return true
		}
		purifier.partition.reals.append(Equal{Left: purifiedLeft, Right: purifiedRight}, false)
		return true
	case RealUnaryComparison:
		if negated {
			return false
		}
		purifier.appendUnaryComparison(value)
		return true
	case RealBinaryComparison:
		if negated {
			return false
		}
		purifier.appendBinaryComparison(value)
		return true
	}
	return purifier.partition.add(term, negated)
}

func (purifier *sharedRealPurifier) appendUnaryComparison(value RealUnaryComparison) {
	result := purifier.unaryApplication(value.FunctionID, value.ArgumentID)
	constraint := LinearRealConstraint{Count: 1, Strict: value.Strict}
	constraint.Symbols[0] = result.ID
	if value.ApplicationOnLeft {
		constraint.Coefficients[0] = NewRational(1, 1)
		constraint.Constant = rationalNeg(value.Bound)
	} else {
		constraint.Coefficients[0] = NewRational(-1, 1)
		constraint.Constant = value.Bound
	}
	purifier.partition.compactReals.append(constraint)
}

func (purifier *sharedRealPurifier) appendBinaryComparison(value RealBinaryComparison) {
	result := purifier.binaryApplication(value.FunctionID, value.FirstArgumentID, value.SecondArgumentID)
	constraint := LinearRealConstraint{Count: 1, Strict: value.Strict}
	constraint.Symbols[0] = result.ID
	if value.ApplicationOnLeft {
		constraint.Coefficients[0] = NewRational(1, 1)
		constraint.Constant = rationalNeg(value.Bound)
	} else {
		constraint.Coefficients[0] = NewRational(-1, 1)
		constraint.Constant = value.Bound
	}
	purifier.partition.compactReals.append(constraint)
}

func (partition *sharedRealPartition) appendSymbolEquality(value RealSymbolEquality) {
	for _, direction := range [2]struct{ left, right int }{{value.LeftID, value.RightID}, {value.RightID, value.LeftID}} {
		constraint := LinearRealConstraint{Count: 2}
		constraint.Symbols[0], constraint.Symbols[1] = direction.left, direction.right
		constraint.Coefficients[0] = NewRational(1, 1)
		constraint.Coefficients[1] = NewRational(-1, 1)
		partition.compactReals.append(constraint)
	}
}

func (purifier *sharedRealPurifier) real(term Term[RealSort]) (Term[RealSort], bool) {
	switch value := term.(type) {
	case Real, RealSymbol:
		return term, true
	case RealAdd:
		items := make([]Term[RealSort], len(value.Values))
		for index, item := range value.Values {
			purified, ok := purifier.real(item)
			if !ok {
				return nil, false
			}
			items[index] = purified
		}
		return RealAdd{Values: items}, true
	case RealSubtract:
		left, leftOK := purifier.real(value.Left)
		right, rightOK := purifier.real(value.Right)
		return RealSubtract{Left: left, Right: right}, leftOK && rightOK
	case RealScale:
		item, ok := purifier.real(value.Value)
		return RealScale{Coefficient: value.Coefficient, Value: item}, ok
	case sortedUnaryApplication[RealSort]:
		function, ok := value.function.(sortedUnaryFunctionValue[RealSort, RealSort])
		argument, argumentOK := value.argument.(Term[RealSort])
		if !ok || !argumentOK || value.rangeKind != -1 {
			return nil, false
		}
		purifiedArgument, ok := purifier.real(argument)
		if !ok {
			return nil, false
		}
		argumentSymbol, isSymbol := purifiedArgument.(RealSymbol)
		if !isSymbol {
			argumentSymbol = RealSymbol{ID: purifier.fresh()}
			purifier.partition.reals.append(Equal{Left: argumentSymbol, Right: purifiedArgument}, false)
		}
		return purifier.unaryApplication(function.iD, argumentSymbol.ID), true
	case sortedBinaryApplication[RealSort]:
		function, ok := value.function.(sortedBinaryFunctionValue[RealSort, RealSort, RealSort])
		first, firstOK := value.first.(Term[RealSort])
		second, secondOK := value.second.(Term[RealSort])
		if !ok || !firstOK || !secondOK || value.rangeKind != -1 {
			return nil, false
		}
		firstSymbol, firstOK := purifier.realArgument(first)
		secondSymbol, secondOK := purifier.realArgument(second)
		if !firstOK || !secondOK {
			return nil, false
		}
		return purifier.binaryApplication(function.iD, firstSymbol.ID, secondSymbol.ID), true
	default:
		return nil, false
	}
}

func (purifier *sharedRealPurifier) realArgument(argument Term[RealSort]) (RealSymbol, bool) {
	purified, ok := purifier.real(argument)
	if !ok {
		return RealSymbol{}, false
	}
	if symbol, ok := purified.(RealSymbol); ok {
		return symbol, true
	}
	symbol := RealSymbol{ID: purifier.fresh()}
	purifier.partition.reals.append(Equal{Left: symbol, Right: purified}, false)
	return symbol, true
}

func (purifier *sharedRealPurifier) unaryApplication(functionID, argumentID int) RealSymbol {
	return purifier.application(1, functionID, argumentID, 0)
}

func (purifier *sharedRealPurifier) binaryApplication(functionID, firstArgumentID, secondArgumentID int) RealSymbol {
	return purifier.application(2, functionID, firstArgumentID, secondArgumentID)
}

func (purifier *sharedRealPurifier) application(arity uint8, functionID, firstArgumentID, secondArgumentID int) RealSymbol {
	for _, application := range purifier.applicationValues() {
		if application.arity == arity && application.functionID == functionID && application.firstArgumentID == firstArgumentID && application.secondArgumentID == secondArgumentID {
			return RealSymbol{ID: application.resultID}
		}
	}
	result := RealSymbol{ID: purifier.fresh()}
	purifier.appendApplication(purifiedApplication{arity: arity, functionID: functionID, firstArgumentID: firstArgumentID, secondArgumentID: secondArgumentID, resultID: result.ID})
	return result
}

func (purifier *sharedRealPurifier) applicationValues() []purifiedApplication {
	if purifier.overflowApplications != nil {
		return purifier.overflowApplications[:purifier.applicationCount]
	}
	return purifier.inlineApplications[:purifier.applicationCount]
}

func (purifier *sharedRealPurifier) appendApplication(value purifiedApplication) {
	if purifier.applicationCount < len(purifier.inlineApplications) && purifier.overflowApplications == nil {
		purifier.inlineApplications[purifier.applicationCount] = value
		purifier.applicationCount++
		return
	}
	if purifier.overflowApplications == nil {
		purifier.overflowApplications = make([]purifiedApplication, purifier.applicationCount, purifier.applicationCount*2)
		copy(purifier.overflowApplications, purifier.inlineApplications[:purifier.applicationCount])
	}
	purifier.overflowApplications = append(purifier.overflowApplications, value)
	purifier.applicationCount++
}

type eufRealNode struct {
	id   int
	node int
}

func containsEUFPair(values []eufPair, left, right int) bool {
	for _, value := range values {
		if value.left == left && value.right == right || value.left == right && value.right == left {
			return true
		}
	}
	return false
}

func linearRealEntailsSymbolEquality(assertions []Term[BoolSort], compact []LinearRealConstraint, leftID, rightID int) bool {
	if linearRealDirectSymbolEquality(assertions, compact, leftID, rightID) {
		return true
	}
	left := RealSymbol{ID: leftID}
	right := RealSymbol{ID: rightID}
	return linearRealUnsatWith(assertions, compact, RealLess{Left: left, Right: right}) &&
		linearRealUnsatWith(assertions, compact, RealLess{Left: right, Right: left})
}

func linearRealDirectSymbolEquality(assertions []Term[BoolSort], compact []LinearRealConstraint, leftID, rightID int) bool {
	leftToRight := false
	rightToLeft := false
	for _, assertion := range assertions {
		switch value := assertion.(type) {
		case Equal:
			left, leftOK := value.Left.(RealSymbol)
			right, rightOK := value.Right.(RealSymbol)
			if leftOK && rightOK && (left.ID == leftID && right.ID == rightID || left.ID == rightID && right.ID == leftID) {
				return true
			}
		case RealSymbolEquality:
			if value.LeftID == leftID && value.RightID == rightID || value.LeftID == rightID && value.RightID == leftID {
				return true
			}
		case RealLessEqual:
			left, leftOK := value.Left.(RealSymbol)
			right, rightOK := value.Right.(RealSymbol)
			if !leftOK || !rightOK {
				continue
			}
			leftToRight = leftToRight || left.ID == leftID && right.ID == rightID
			rightToLeft = rightToLeft || left.ID == rightID && right.ID == leftID
		}
	}
	for _, constraint := range compact {
		leftToRight = leftToRight || compactOrdersSymbols(constraint, leftID, rightID)
		rightToLeft = rightToLeft || compactOrdersSymbols(constraint, rightID, leftID)
	}
	return leftToRight && rightToLeft
}

func compactOrdersSymbols(constraint LinearRealConstraint, leftID, rightID int) bool {
	if constraint.Strict || constraint.Constant.Sign() != 0 || constraint.Count != 2 {
		return false
	}
	symbols, coefficients := constraint.coefficientValues()
	var left, right Rational
	leftFound := false
	rightFound := false
	for index, id := range symbols {
		switch id {
		case leftID:
			left, leftFound = coefficients[index], true
		case rightID:
			right, rightFound = coefficients[index], true
		}
	}
	return leftFound && rightFound && left.Sign() > 0 && rationalCmp(left, rationalNeg(right)) == 0
}

func linearRealUnsatWith(assertions []Term[BoolSort], compact []LinearRealConstraint, extra Term[BoolSort]) bool {
	if len(assertions)+1 <= 16 {
		var inline [16]Term[BoolSort]
		copy(inline[:], assertions)
		inline[len(assertions)] = extra
		outcome, recognized := solveLinearRealParts(inline[:len(assertions)+1], compact)
		return recognized && outcome.status == checkUnsat
	}
	combined := make([]Term[BoolSort], len(assertions)+1)
	copy(combined, assertions)
	combined[len(assertions)] = extra
	outcome, recognized := solveLinearRealParts(combined, compact)
	return recognized && outcome.status == checkUnsat
}

type sharedRealPartition struct {
	euf          theoryTerms
	reals        theoryTerms
	compactReals compactRealTerms
	unsat        bool
}

func (partition *sharedRealPartition) add(term Term[BoolSort], negated bool) bool {
	switch value := term.(type) {
	case Bool:
		partition.unsat = partition.unsat || value.Value == negated
		return true
	case And:
		if negated {
			return false
		}
		for _, item := range value.Values {
			if !partition.add(item, false) {
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
			if !partition.add(item, polarities[index]) {
				return false
			}
		}
		return true
	case TheoryConjunction:
		if negated {
			return false
		}
		terms, polarities := value.atomValues()
		for index, item := range terms {
			if !partition.add(item, polarities[index]) {
				return false
			}
		}
		for _, constraint := range value.realValues() {
			partition.compactReals.append(constraint)
		}
		for _, equality := range value.symbolEqualityValues() {
			partition.appendSymbolEquality(equality)
		}
		for _, comparison := range value.unaryComparisonValues() {
			partition.euf.append(comparison, false)
		}
		for _, comparison := range value.binaryComparisonValues() {
			partition.euf.append(comparison, false)
		}
		return true
	case Not:
		return partition.add(value.Value, !negated)
	}
	if containsEUF(term) {
		partition.euf.append(term, negated)
		return true
	}
	if containsRealTheory(term) && !negated {
		partition.reals.append(term, false)
		return true
	}
	return false
}

// solveConjunctiveTheoryProduct decides conjunctions whose atoms belong to
// disjoint array, bit-vector, EUF, integer-difference, and linear-real signatures. Because the
// current typed function surface only accepts UninterpretedSort arguments,
// no term can be shared with arithmetic yet; independent decision procedures
// are therefore sound and complete for this fragment.
func solveConjunctiveTheoryProduct(assertions []Term[BoolSort]) (checkOutcome, bool) {
	partition := theoryPartition{}
	for _, assertion := range assertions {
		if !partition.add(assertion, false) {
			return checkOutcome{}, false
		}
	}
	if partition.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	if partition.hasSharedArrayInteger() {
		return checkOutcome{}, false
	}
	active := 0
	if partition.euf.count != 0 {
		active++
	}
	if partition.integers.count != 0 {
		active++
	}
	if partition.reals.count != 0 || partition.compactReals.count != 0 {
		active++
	}
	if partition.arrays.count != 0 {
		active++
	}
	if partition.bitVectors.count != 0 {
		active++
	}
	if active < 2 {
		return checkOutcome{}, false
	}
	combined := checkOutcome{status: checkSat}
	if partition.arrays.count != 0 {
		terms, _ := partition.arrays.values()
		outcome, recognized := solveArrayAssertions(terms)
		if !recognized {
			return checkOutcome{}, false
		}
		if outcome.status == checkUnsat {
			return outcome, true
		}
		combined.arrays = outcome.arrays
		combined.integers.merge(outcome.integers)
	}
	if partition.bitVectors.count != 0 {
		terms, _ := partition.bitVectors.values()
		outcome, recognized := solveBitVectorAssertions(terms)
		if !recognized {
			return checkOutcome{}, false
		}
		if outcome.status == checkUnsat {
			return outcome, true
		}
		combined.bitVectors = outcome.bitVectors
	}
	if partition.euf.count != 0 {
		terms, negated := partition.euf.values()
		var inlineTerms [16]Term[BoolSort]
		var inlineNegated [16]bool
		exchangedTerms := inlineTerms[:0]
		exchangedNegated := inlineNegated[:0]
		exchangedTerms = append(exchangedTerms, terms...)
		exchangedNegated = append(exchangedNegated, negated...)
		if partition.integers.count != 0 {
			integerTerms, integerNegated := partition.integers.values()
			for index, term := range integerTerms {
				equality, ok := term.(Equal)
				if !ok {
					continue
				}
				left, leftOK := equality.Left.(Term[IntSort])
				right, rightOK := equality.Right.(Term[IntSort])
				if !leftOK || !rightOK {
					continue
				}
				if _, _, leftOK = IntegerSymbol(left); !leftOK {
					continue
				}
				if _, _, rightOK = IntegerSymbol(right); !rightOK {
					continue
				}
				exchangedTerms = append(exchangedTerms, term)
				exchangedNegated = append(exchangedNegated, integerNegated[index])
			}
		}
		outcome, recognized := solveEUFPolarized(exchangedTerms, exchangedNegated)
		if !recognized {
			return checkOutcome{}, false
		}
		if outcome.status == checkUnsat {
			return outcome, true
		}
	}
	if partition.integers.count != 0 {
		terms, _ := partition.integers.values()
		outcome, recognized := checkOutcome{}, false
		if containsGeneralLinearIntegerAssertions(terms) {
			outcome, recognized = solveLinearIntegerAssertions(terms)
		}
		if !recognized {
			outcome, recognized = solveDifferenceAssertions(terms)
		}
		if !recognized {
			outcome, recognized = solveLinearIntegerAssertions(terms)
		}
		if !recognized {
			outcome, recognized = solveBooleanLinearIntegerAssertions(terms)
		}
		if !recognized {
			return checkOutcome{}, false
		}
		if outcome.status == checkUnsat {
			return outcome, true
		}
		combined.integers.merge(outcome.integers)
	}
	if partition.reals.count != 0 || partition.compactReals.count != 0 {
		terms, _ := partition.reals.values()
		outcome, recognized := solveLinearRealParts(terms, partition.compactReals.values())
		if !recognized {
			return checkOutcome{}, false
		}
		if outcome.status == checkUnsat {
			return outcome, true
		}
		combined.reals = outcome.reals
	}
	return combined, true
}

func solveSharedArrayInteger(assertions []Term[BoolSort]) (checkOutcome, bool) {
	partition := theoryPartition{}
	for _, assertion := range assertions {
		if !partition.add(assertion, false) {
			return checkOutcome{}, false
		}
	}
	if partition.arrays.count == 0 || partition.integers.count == 0 || !partition.hasSharedArrayInteger() || partition.bitVectors.count != 0 || partition.euf.count != 0 || partition.reals.count != 0 || partition.compactReals.count != 0 {
		return checkOutcome{}, false
	}
	integerTerms, _ := partition.integers.values()
	integerOutcome, recognized := solveDifferenceAssertions(integerTerms)
	if !recognized {
		return checkOutcome{}, false
	}
	if integerOutcome.status == checkUnsat {
		return integerOutcome, true
	}
	for left := 0; left < partition.arrayIntegerCount; left++ {
		for right := left + 1; right < partition.arrayIntegerCount; right++ {
			entailed, recognized := differenceEntailsEquality(integerTerms, partition.arrayIntegerIDs[left], partition.arrayIntegerIDs[right])
			if !recognized {
				return checkOutcome{}, false
			}
			if entailed {
				partition.arrays.append(Equal{Left: integerVariable[IntSort]{iD: partition.arrayIntegerIDs[left]}, Right: integerVariable[IntSort]{iD: partition.arrayIntegerIDs[right]}}, false)
			}
		}
	}
	arrayTerms, _ := partition.arrays.values()
	arrayOutcome, recognized := solveGroundArrayCongruenceWithIntegers(arrayTerms, integerOutcome.integers)
	if !recognized {
		return checkOutcome{}, false
	}
	return arrayOutcome, true
}

type theoryPartition struct {
	arrays            theoryTerms
	bitVectors        theoryTerms
	euf               theoryTerms
	integers          theoryTerms
	reals             theoryTerms
	compactReals      compactRealTerms
	arrayIntegerCount int
	arrayIntegerIDs   [16]int
	integerCount      int
	integerIDs        [16]int
	unsat             bool
}

type compactRealTerms struct {
	count    int
	inline   [8]LinearRealConstraint
	overflow []LinearRealConstraint
}

func (terms *compactRealTerms) append(value LinearRealConstraint) {
	if terms.count < len(terms.inline) && terms.overflow == nil {
		terms.inline[terms.count] = value
		terms.count++
		return
	}
	if terms.overflow == nil {
		terms.overflow = make([]LinearRealConstraint, terms.count, terms.count*2)
		copy(terms.overflow, terms.inline[:terms.count])
	}
	terms.overflow = append(terms.overflow, value)
	terms.count++
}

func (terms *compactRealTerms) values() []LinearRealConstraint {
	if terms.overflow != nil {
		return terms.overflow[:terms.count]
	}
	return terms.inline[:terms.count]
}

type theoryTerms struct {
	count           int
	inlineTerms     [8]Term[BoolSort]
	inlineNegated   [8]bool
	overflowTerms   []Term[BoolSort]
	overflowNegated []bool
}

func (terms *theoryTerms) append(term Term[BoolSort], negated bool) {
	if terms.count < len(terms.inlineTerms) && terms.overflowTerms == nil {
		terms.inlineTerms[terms.count] = term
		terms.inlineNegated[terms.count] = negated
		terms.count++
		return
	}
	if terms.overflowTerms == nil {
		terms.overflowTerms = make([]Term[BoolSort], terms.count, terms.count*2)
		terms.overflowNegated = make([]bool, terms.count, terms.count*2)
		copy(terms.overflowTerms, terms.inlineTerms[:terms.count])
		copy(terms.overflowNegated, terms.inlineNegated[:terms.count])
	}
	terms.overflowTerms = append(terms.overflowTerms, term)
	terms.overflowNegated = append(terms.overflowNegated, negated)
	terms.count++
}

func (terms *theoryTerms) values() ([]Term[BoolSort], []bool) {
	if terms.overflowTerms != nil {
		return terms.overflowTerms[:terms.count], terms.overflowNegated[:terms.count]
	}
	return terms.inlineTerms[:terms.count], terms.inlineNegated[:terms.count]
}

func (partition *theoryPartition) add(term Term[BoolSort], negated bool) bool {
	switch value := term.(type) {
	case Bool:
		partition.unsat = partition.unsat || value.Value == negated
		return true
	case And:
		if negated {
			return false
		}
		for _, item := range value.Values {
			if !partition.add(item, false) {
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
			if !partition.add(item, polarities[index]) {
				return false
			}
		}
		return true
	case TheoryConjunction:
		if negated {
			return false
		}
		atoms, polarities := value.atomValues()
		for index, item := range atoms {
			if !partition.add(item, polarities[index]) {
				return false
			}
		}
		for _, constraint := range value.realValues() {
			partition.compactReals.append(constraint)
		}
		for _, equality := range value.symbolEqualityValues() {
			partition.reals.append(equality, false)
		}
		for _, comparison := range value.unaryComparisonValues() {
			partition.euf.append(comparison, false)
		}
		for _, comparison := range value.binaryComparisonValues() {
			partition.euf.append(comparison, false)
		}
		return true
	case Not:
		return partition.add(value.Value, !negated)
	}
	integer := containsIntegerTheory(term)
	array := containsArrayTheory(term)
	bitVector := containsBitVectorTheory(term)
	euf := containsEUF(term)
	real := containsRealTheory(term)
	count := 0
	if array {
		count++
	} else if bitVector {
		count++
	} else if integer {
		count++
	}
	if euf {
		count++
	}
	if real {
		count++
	}
	if count != 1 {
		return false
	}
	switch {
	case array:
		collectTheoryIntegerIDs(term, func(id int) { partition.addArrayIntegerID(id) })
		if negated {
			partition.arrays.append(Not{Value: term}, false)
		} else {
			partition.arrays.append(term, false)
		}
	case bitVector:
		if negated {
			partition.bitVectors.append(Not{Value: term}, false)
		} else {
			partition.bitVectors.append(term, false)
		}
	case integer:
		collectTheoryIntegerIDs(term, func(id int) { partition.addIntegerID(id) })
		if negated {
			return false
		}
		partition.integers.append(term, false)
	case euf:
		partition.euf.append(term, negated)
	case real:
		if negated {
			return false
		}
		partition.reals.append(term, false)
	}
	return true
}

func (partition *theoryPartition) addArrayIntegerID(id int) {
	for _, existing := range partition.arrayIntegerIDs[:partition.arrayIntegerCount] {
		if existing == id {
			return
		}
	}
	if partition.arrayIntegerCount < len(partition.arrayIntegerIDs) {
		partition.arrayIntegerIDs[partition.arrayIntegerCount] = id
		partition.arrayIntegerCount++
	}
}

func (partition *theoryPartition) addIntegerID(id int) {
	for _, existing := range partition.integerIDs[:partition.integerCount] {
		if existing == id {
			return
		}
	}
	if partition.integerCount < len(partition.integerIDs) {
		partition.integerIDs[partition.integerCount] = id
		partition.integerCount++
	}
}

func (partition *theoryPartition) hasSharedArrayInteger() bool {
	for _, arrayID := range partition.arrayIntegerIDs[:partition.arrayIntegerCount] {
		for _, integerID := range partition.integerIDs[:partition.integerCount] {
			if arrayID == integerID {
				return true
			}
		}
	}
	return false
}

func collectTheoryIntegerIDs(term any, add func(int)) {
	switch value := term.(type) {
	case And:
		for _, item := range value.Values {
			collectTheoryIntegerIDs(item, add)
		}
	case Or:
		for _, item := range value.Values {
			collectTheoryIntegerIDs(item, add)
		}
	case BooleanConjunction:
		terms, _ := value.values()
		for _, item := range terms {
			collectTheoryIntegerIDs(item, add)
		}
	case Implies:
		collectTheoryIntegerIDs(value.Left, add)
		collectTheoryIntegerIDs(value.Right, add)
	case Iff:
		collectTheoryIntegerIDs(value.Left, add)
		collectTheoryIntegerIDs(value.Right, add)
	case IntSymbol:
		add(value.ID)
	case integerVariable[IntSort]:
		add(value.iD)
	case Equal:
		collectTheoryIntegerIDs(value.Left, add)
		collectTheoryIntegerIDs(value.Right, add)
	case LessEqual:
		collectTheoryIntegerIDs(value.Left, add)
		collectTheoryIntegerIDs(value.Right, add)
	case Less:
		collectTheoryIntegerIDs(value.Left, add)
		collectTheoryIntegerIDs(value.Right, add)
	case Add:
		for _, item := range value.Values {
			collectTheoryIntegerIDs(item, add)
		}
	case Subtract:
		collectTheoryIntegerIDs(value.Left, add)
		collectTheoryIntegerIDs(value.Right, add)
	case IntegerScale:
		collectTheoryIntegerIDs(value.Value, add)
	case IntegerDiv:
		collectTheoryIntegerIDs(value.Dividend, add)
	case IntegerMod:
		collectTheoryIntegerIDs(value.Dividend, add)
	case Not:
		collectTheoryIntegerIDs(value.Value, add)
	case arraySelectionTerm:
		array, index := value.arraySelectionParts()
		collectTheoryIntegerIDs(array, add)
		collectTheoryIntegerIDs(index, add)
	case arrayStoreTerm:
		array, index, stored := value.arrayStoreParts()
		collectTheoryIntegerIDs(array, add)
		collectTheoryIntegerIDs(index, add)
		collectTheoryIntegerIDs(stored, add)
	case arrayStoreReadInteger[IntSort]:
		add(value.storeIndexID)
		add(value.readIndexID)
	case ArrayStoreReadValueRelation:
		add(value.StoreIndexID)
		add(value.ReadIndexID)
	case ArrayIntegerEqualityExchange:
		collectTheoryIntegerIDs(value.First, add)
		collectTheoryIntegerIDs(value.Second, add)
		collectTheoryIntegerIDs(value.Read, add)
	case IntegerDifferenceConstraint:
		if value.HasPositive {
			add(value.PositiveID)
		}
		if value.HasNegative {
			add(value.NegativeID)
		}
	case IntegerDifferenceSystem:
		for _, constraint := range value.values() {
			collectTheoryIntegerIDs(constraint, add)
		}
	case IntegerLinearEquality:
		add(value.ID)
	case IntegerLinearDisequality:
		add(value.Equality.ID)
	case IntegerLinearChoice:
		add(value.First.ID)
		add(value.Second.ID)
	}
}
