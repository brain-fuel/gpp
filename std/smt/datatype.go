package smt

// DatatypeValue is the exact model value of a finite enumeration datatype.
// IDs are declaration-local ordinals; ConstructorName is retained when the
// corresponding constructor appeared in the authored formula.
type DatatypeValue struct {
	DatatypeID       int
	ConstructorCount int
	ConstructorID    int
	ConstructorName  string
}

type datatypeModelEntry struct {
	datatypeID int
	symbolID   int
	value      DatatypeValue
}

type datatypeModel struct {
	count    int
	inline   [8]datatypeModelEntry
	overflow map[[2]int]DatatypeValue
}

func (model *datatypeModel) set(datatypeID, symbolID int, value DatatypeValue) {
	for index := 0; index < model.count; index++ {
		if model.inline[index].datatypeID == datatypeID && model.inline[index].symbolID == symbolID {
			model.inline[index].value = value
			return
		}
	}
	if model.count < len(model.inline) {
		model.inline[model.count] = datatypeModelEntry{datatypeID: datatypeID, symbolID: symbolID, value: value}
		model.count++
		return
	}
	if model.overflow == nil {
		model.overflow = make(map[[2]int]DatatypeValue)
	}
	model.overflow[[2]int{datatypeID, symbolID}] = value
}

func (model datatypeModel) lookup(datatypeID, symbolID int) (DatatypeValue, bool) {
	for index := 0; index < model.count; index++ {
		entry := model.inline[index]
		if entry.datatypeID == datatypeID && entry.symbolID == symbolID {
			return entry.value, true
		}
	}
	value, ok := model.overflow[[2]int{datatypeID, symbolID}]
	return value, ok
}

func evaluateDatatype(term Term[DatatypeSort], model datatypeModel) (DatatypeValue, bool) {
	switch value := term.(type) {
	case datatypeConstructor[DatatypeSort]:
		return DatatypeValue{DatatypeID: value.datatypeID, ConstructorCount: value.constructorCount, ConstructorID: value.constructorID, ConstructorName: value.name}, true
	case datatypeSymbol[DatatypeSort]:
		return model.lookup(value.datatypeID, value.iD)
	default:
		return DatatypeValue{}, false
	}
}

func evaluateBoolWithDatatypes(term Term[BoolSort], booleans booleanModel, integers integerModel, reals rationalModel, datatypes datatypeModel) (bool, bool) {
	switch value := term.(type) {
	case datatypeRecognizer:
		candidate, ok := value.value.(Term[DatatypeSort])
		if !ok {
			return false, false
		}
		actual, found := evaluateDatatype(candidate, datatypes)
		return actual.ConstructorID == value.constructorID, found && actual.DatatypeID == value.datatypeID && actual.ConstructorCount == value.constructorCount
	case Equal:
		left, leftOK := value.Left.(Term[DatatypeSort])
		right, rightOK := value.Right.(Term[DatatypeSort])
		if leftOK && rightOK {
			leftValue, leftFound := evaluateDatatype(left, datatypes)
			rightValue, rightFound := evaluateDatatype(right, datatypes)
			return leftValue.DatatypeID == rightValue.DatatypeID && leftValue.ConstructorCount == rightValue.ConstructorCount && leftValue.ConstructorID == rightValue.ConstructorID, leftFound && rightFound
		}
	case Not:
		result, ok := evaluateBoolWithDatatypes(value.Value, booleans, integers, reals, datatypes)
		return !result, ok
	case And:
		for _, item := range value.Values {
			result, ok := evaluateBoolWithDatatypes(item, booleans, integers, reals, datatypes)
			if !ok || !result {
				return result, ok
			}
		}
		return true, true
	case BooleanConjunction:
		items, negated := value.values()
		for index, item := range items {
			result, ok := evaluateBoolWithDatatypes(item, booleans, integers, reals, datatypes)
			if !ok || result == negated[index] {
				return false, ok
			}
		}
		return true, true
	case Or:
		for _, item := range value.Values {
			result, ok := evaluateBoolWithDatatypes(item, booleans, integers, reals, datatypes)
			if !ok {
				return false, false
			}
			if result {
				return true, true
			}
		}
		return false, true
	case Implies:
		left, leftOK := evaluateBoolWithDatatypes(value.Left, booleans, integers, reals, datatypes)
		right, rightOK := evaluateBoolWithDatatypes(value.Right, booleans, integers, reals, datatypes)
		return !left || right, leftOK && rightOK
	case Iff:
		left, leftOK := evaluateBoolWithDatatypes(value.Left, booleans, integers, reals, datatypes)
		right, rightOK := evaluateBoolWithDatatypes(value.Right, booleans, integers, reals, datatypes)
		return left == right, leftOK && rightOK
	}
	return evaluateBool(term, booleans, integers, reals)
}

type datatypeNode struct {
	datatypeID       int
	constructorCount int
	kind             uint8
	id               int
	name             string
}

type datatypePair struct{ left, right int }

type datatypeProblem struct {
	nodes               []datatypeNode
	parents             []int
	ranks               []uint8
	disequalities       []datatypePair
	unsat               bool
	inlineNodes         [8]datatypeNode
	inlineParents       [8]int
	inlineRanks         [8]uint8
	inlineDisequalities [8]datatypePair
}

func containsDatatypeTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case Equal:
		return isDatatypeTerm(value.Left) || isDatatypeTerm(value.Right)
	case datatypeRecognizer:
		return true
	case Not:
		return containsDatatypeTheory(value.Value)
	case And:
		for _, item := range value.Values {
			if containsDatatypeTheory(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsDatatypeTheory(item) {
				return true
			}
		}
	}
	return false
}

func isDatatypeTerm(term any) bool {
	switch term.(type) {
	case datatypeSymbol[DatatypeSort], datatypeConstructor[DatatypeSort]:
		return true
	default:
		return false
	}
}

func solveDatatypeAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	problem := datatypeProblem{}
	problem.nodes = problem.inlineNodes[:0]
	problem.parents = problem.inlineParents[:0]
	problem.ranks = problem.inlineRanks[:0]
	problem.disequalities = problem.inlineDisequalities[:0]
	for _, assertion := range assertions {
		if !problem.boolean(assertion, false) {
			return checkOutcome{}, false
		}
	}
	if problem.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	return problem.solve()
}

func (problem *datatypeProblem) boolean(term Term[BoolSort], negated bool) bool {
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
		items, polarities := value.values()
		for index, item := range items {
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
		if !leftOK || !rightOK || !problem.compatible(left, right) {
			return false
		}
		if negated {
			problem.disequalities = append(problem.disequalities, datatypePair{left: left, right: right})
		} else {
			problem.union(left, right)
		}
		return true
	case datatypeRecognizer:
		candidate, ok := problem.term(value.value)
		if !ok || problem.nodes[candidate].datatypeID != value.datatypeID || problem.nodes[candidate].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return false
		}
		constructor := problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 1, id: value.constructorID})
		if negated {
			problem.disequalities = append(problem.disequalities, datatypePair{left: candidate, right: constructor})
		} else {
			problem.union(candidate, constructor)
		}
		return true
	default:
		return false
	}
}

func (problem *datatypeProblem) term(term any) (int, bool) {
	switch value := term.(type) {
	case datatypeSymbol[DatatypeSort]:
		if value.constructorCount <= 0 {
			return 0, false
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, id: value.iD, name: value.name}), true
	case datatypeConstructor[DatatypeSort]:
		if value.constructorCount <= 0 || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return 0, false
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 1, id: value.constructorID, name: value.name}), true
	default:
		return 0, false
	}
}

func (problem *datatypeProblem) ensure(node datatypeNode) int {
	for index, existing := range problem.nodes {
		if existing.datatypeID == node.datatypeID && existing.constructorCount == node.constructorCount && existing.kind == node.kind && existing.id == node.id {
			if problem.nodes[index].name == "" {
				problem.nodes[index].name = node.name
			}
			return index
		}
	}
	index := len(problem.nodes)
	problem.nodes = append(problem.nodes, node)
	problem.parents = append(problem.parents, index)
	problem.ranks = append(problem.ranks, 0)
	return index
}

func (problem *datatypeProblem) compatible(left, right int) bool {
	return problem.nodes[left].datatypeID == problem.nodes[right].datatypeID && problem.nodes[left].constructorCount == problem.nodes[right].constructorCount
}

func (problem *datatypeProblem) find(node int) int {
	root := node
	for problem.parents[root] != root {
		root = problem.parents[root]
	}
	for problem.parents[node] != node {
		next := problem.parents[node]
		problem.parents[node] = root
		node = next
	}
	return root
}

func (problem *datatypeProblem) union(left, right int) {
	left, right = problem.find(left), problem.find(right)
	if left == right {
		return
	}
	leftNode, rightNode := problem.nodes[left], problem.nodes[right]
	if !problem.compatible(left, right) || leftNode.kind == 1 && rightNode.kind == 1 && leftNode.id != rightNode.id {
		problem.unsat = true
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

func (problem *datatypeProblem) solve() (checkOutcome, bool) {
	if problem.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	for _, pair := range problem.disequalities {
		if problem.find(pair.left) == problem.find(pair.right) {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	assignment := make([]int, len(problem.nodes))
	for index := range assignment {
		assignment[index] = -1
	}
	for index, node := range problem.nodes {
		if node.kind == 1 {
			root := problem.find(index)
			if assignment[root] >= 0 && assignment[root] != node.id {
				return checkOutcome{status: checkUnsat}, true
			}
			assignment[root] = node.id
		}
	}
	roots := make([]int, 0, len(problem.nodes))
	for index := range problem.nodes {
		root := problem.find(index)
		if root == index && problem.nodes[index].kind == 0 {
			roots = append(roots, root)
		}
	}
	if !problem.color(roots, 0, assignment) {
		return checkOutcome{status: checkUnsat}, true
	}
	var model datatypeModel
	for index, node := range problem.nodes {
		if node.kind != 0 {
			continue
		}
		constructorID := assignment[problem.find(index)]
		model.set(node.datatypeID, node.id, DatatypeValue{DatatypeID: node.datatypeID, ConstructorCount: node.constructorCount, ConstructorID: constructorID, ConstructorName: problem.constructorName(node.datatypeID, node.constructorCount, constructorID)})
	}
	return checkOutcome{status: checkSat, datatypes: model}, true
}

func (problem *datatypeProblem) color(roots []int, position int, assignment []int) bool {
	if position == len(roots) {
		return true
	}
	root := roots[position]
	if assignment[root] >= 0 {
		if problem.assignmentAllowed(root, assignment[root], assignment) {
			return problem.color(roots, position+1, assignment)
		}
		return false
	}
	for constructor := 0; constructor < problem.nodes[root].constructorCount; constructor++ {
		if problem.assignmentAllowed(root, constructor, assignment) {
			assignment[root] = constructor
			if problem.color(roots, position+1, assignment) {
				return true
			}
			assignment[root] = -1
		}
	}
	return false
}

func (problem *datatypeProblem) assignmentAllowed(root, constructor int, assignment []int) bool {
	for _, pair := range problem.disequalities {
		left, right := problem.find(pair.left), problem.find(pair.right)
		if left == root && assignment[right] == constructor || right == root && assignment[left] == constructor {
			return false
		}
	}
	return true
}

func (problem *datatypeProblem) constructorName(datatypeID, constructorCount, constructorID int) string {
	for _, node := range problem.nodes {
		if node.kind == 1 && node.datatypeID == datatypeID && node.constructorCount == constructorCount && node.id == constructorID {
			return node.name
		}
	}
	return ""
}
