package smt

const datatypeBooleanBranchLimit = 256

type datatypeBooleanBranches struct {
	count     int
	inline    [4]datatypeBooleanBranch
	overflow  []datatypeBooleanBranch
	exhausted bool
}

type datatypeBooleanBranch struct {
	count    int
	inline   [8]Term[BoolSort]
	overflow []Term[BoolSort]
}

func (branches *datatypeBooleanBranches) append(branch datatypeBooleanBranch) {
	if branches.count >= datatypeBooleanBranchLimit {
		branches.exhausted = true
		return
	}
	if branches.count < len(branches.inline) && branches.overflow == nil {
		branches.inline[branches.count] = branch
		branches.count++
		return
	}
	if branches.overflow == nil {
		branches.overflow = make([]datatypeBooleanBranch, branches.count, branches.count*2)
		copy(branches.overflow, branches.inline[:branches.count])
	}
	branches.overflow = append(branches.overflow, branch)
	branches.count++
}

func (branches *datatypeBooleanBranches) branches() []datatypeBooleanBranch {
	if branches.overflow != nil {
		return branches.overflow[:branches.count]
	}
	return branches.inline[:branches.count]
}

func (branch *datatypeBooleanBranch) append(atom Term[BoolSort]) {
	if branch.count < len(branch.inline) && branch.overflow == nil {
		branch.inline[branch.count] = atom
		branch.count++
		return
	}
	if branch.overflow == nil {
		branch.overflow = make([]Term[BoolSort], branch.count, branch.count*2)
		copy(branch.overflow, branch.inline[:branch.count])
	}
	branch.overflow = append(branch.overflow, atom)
	branch.count++
}

func (branch *datatypeBooleanBranch) atoms() []Term[BoolSort] {
	if branch.overflow != nil {
		return branch.overflow[:branch.count]
	}
	return branch.inline[:branch.count]
}

func appendDatatypeBooleanAtoms(first, second datatypeBooleanBranch) datatypeBooleanBranch {
	result := datatypeBooleanBranch{}
	total := first.count + second.count
	if total > len(result.inline) {
		result.overflow = make([]Term[BoolSort], 0, total)
	}
	for _, atom := range first.atoms() {
		result.append(atom)
	}
	for _, atom := range second.atoms() {
		result.append(atom)
	}
	return result
}

func solveBooleanDatatypeAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	branches := datatypeBooleanBranches{}
	branches.append(datatypeBooleanBranch{})
	for _, assertion := range assertions {
		next, ok := normalizeDatatypeBoolean(assertion, true)
		if !ok {
			return checkOutcome{}, false
		}
		branches = combineDatatypeBooleanBranches(branches, next)
		if branches.exhausted {
			return checkOutcome{status: checkUnknown, reason: ResourceLimit{Limit: datatypeBooleanBranchLimit}}, true
		}
	}
	var unknown checkOutcome
	unknownSeen := false
	for _, branch := range branches.branches() {
		outcome, recognized := solveDatatypeAssertions(branch.atoms())
		if !recognized {
			return checkOutcome{}, false
		}
		if outcome.status == checkSat {
			return outcome, true
		}
		if outcome.status == checkUnknown && !unknownSeen {
			unknown, unknownSeen = outcome, true
		}
	}
	if unknownSeen {
		return unknown, true
	}
	return checkOutcome{status: checkUnsat}, true
}

func containsBooleanDatatypeAssertions(assertions []Term[BoolSort]) bool {
	for _, assertion := range assertions {
		if containsBooleanDatatype(assertion) {
			return true
		}
	}
	return false
}

func containsBooleanDatatype(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case Or, Implies, Iff, If[BoolSort]:
		return containsDatatypeTheory(term)
	case Not:
		return containsBooleanDatatype(value.Value)
	case And:
		for _, item := range value.Values {
			if containsBooleanDatatype(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsBooleanDatatype(item) {
				return true
			}
		}
	case Equal:
		left, leftOK := value.Left.(Term[BoolSort])
		right, rightOK := value.Right.(Term[BoolSort])
		return leftOK && rightOK && (containsDatatypeTheory(left) || containsDatatypeTheory(right))
	}
	return false
}

func normalizeDatatypeBoolean(term Term[BoolSort], positive bool) (datatypeBooleanBranches, bool) {
	switch value := term.(type) {
	case Bool:
		if value.Value == positive {
			result := datatypeBooleanBranches{}
			result.append(datatypeBooleanBranch{})
			return result, true
		}
		return datatypeBooleanBranches{}, true
	case Not:
		return normalizeDatatypeBoolean(value.Value, !positive)
	case And:
		return normalizeDatatypeBooleanMany(value.Values, positive, positive)
	case Or:
		return normalizeDatatypeBooleanMany(value.Values, positive, !positive)
	case Implies:
		if positive {
			left, leftOK := normalizeDatatypeBoolean(value.Left, false)
			right, rightOK := normalizeDatatypeBoolean(value.Right, true)
			return unionDatatypeBooleanBranches(left, right), leftOK && rightOK
		}
		left, leftOK := normalizeDatatypeBoolean(value.Left, true)
		right, rightOK := normalizeDatatypeBoolean(value.Right, false)
		return combineDatatypeBooleanBranches(left, right), leftOK && rightOK
	case Iff:
		return normalizeDatatypeEquivalence(value.Left, value.Right, positive)
	case If[BoolSort]:
		conditionTrue, firstOK := normalizeDatatypeBoolean(value.Condition, true)
		conditionFalse, secondOK := normalizeDatatypeBoolean(value.Condition, false)
		thenBranch, thirdOK := normalizeDatatypeBoolean(value.Then, positive)
		elseBranch, fourthOK := normalizeDatatypeBoolean(value.Else, positive)
		return unionDatatypeBooleanBranches(
			combineDatatypeBooleanBranches(conditionTrue, thenBranch),
			combineDatatypeBooleanBranches(conditionFalse, elseBranch),
		), firstOK && secondOK && thirdOK && fourthOK
	case BooleanConjunction:
		items, negated := value.values()
		result := datatypeBooleanBranches{}
		if positive {
			result.append(datatypeBooleanBranch{})
		}
		for index, item := range items {
			part, ok := normalizeDatatypeBoolean(item, positive != negated[index])
			if !ok {
				return datatypeBooleanBranches{}, false
			}
			if positive {
				result = combineDatatypeBooleanBranches(result, part)
			} else {
				result = unionDatatypeBooleanBranches(result, part)
			}
		}
		return result, true
	case Equal:
		left, leftOK := value.Left.(Term[BoolSort])
		right, rightOK := value.Right.(Term[BoolSort])
		if leftOK && rightOK {
			return normalizeDatatypeEquivalence(left, right, positive)
		}
		return datatypeBooleanAtom(term, positive)
	default:
		return datatypeBooleanAtom(term, positive)
	}
}

func normalizeDatatypeEquivalence(left, right Term[BoolSort], positive bool) (datatypeBooleanBranches, bool) {
	leftTrue, firstOK := normalizeDatatypeBoolean(left, true)
	rightTrue, secondOK := normalizeDatatypeBoolean(right, true)
	leftFalse, thirdOK := normalizeDatatypeBoolean(left, false)
	rightFalse, fourthOK := normalizeDatatypeBoolean(right, false)
	if positive {
		return unionDatatypeBooleanBranches(
			combineDatatypeBooleanBranches(leftTrue, rightTrue),
			combineDatatypeBooleanBranches(leftFalse, rightFalse),
		), firstOK && secondOK && thirdOK && fourthOK
	}
	return unionDatatypeBooleanBranches(
		combineDatatypeBooleanBranches(leftTrue, rightFalse),
		combineDatatypeBooleanBranches(leftFalse, rightTrue),
	), firstOK && secondOK && thirdOK && fourthOK
}

func normalizeDatatypeBooleanMany(terms []Term[BoolSort], childPositive, conjunction bool) (datatypeBooleanBranches, bool) {
	result := datatypeBooleanBranches{}
	if conjunction {
		result.append(datatypeBooleanBranch{})
	}
	for _, term := range terms {
		part, ok := normalizeDatatypeBoolean(term, childPositive)
		if !ok {
			return datatypeBooleanBranches{}, false
		}
		if conjunction {
			result = combineDatatypeBooleanBranches(result, part)
		} else {
			result = unionDatatypeBooleanBranches(result, part)
		}
		if result.exhausted {
			break
		}
	}
	return result, true
}

func datatypeBooleanAtom(term Term[BoolSort], positive bool) (datatypeBooleanBranches, bool) {
	if !containsDatatypeTheory(term) {
		return datatypeBooleanBranches{}, false
	}
	if !positive {
		term = Not{Value: term}
	}
	branch := datatypeBooleanBranch{}
	branch.append(term)
	result := datatypeBooleanBranches{}
	result.append(branch)
	return result, true
}

func unionDatatypeBooleanBranches(left, right datatypeBooleanBranches) datatypeBooleanBranches {
	if left.exhausted || right.exhausted || left.count+right.count > datatypeBooleanBranchLimit {
		return datatypeBooleanBranches{exhausted: true}
	}
	result := datatypeBooleanBranches{}
	for _, branch := range left.branches() {
		result.append(branch)
	}
	for _, branch := range right.branches() {
		result.append(branch)
	}
	return result
}

func combineDatatypeBooleanBranches(left, right datatypeBooleanBranches) datatypeBooleanBranches {
	if left.exhausted || right.exhausted || left.count != 0 && right.count > datatypeBooleanBranchLimit/left.count {
		return datatypeBooleanBranches{exhausted: true}
	}
	result := datatypeBooleanBranches{}
	for _, first := range left.branches() {
		for _, second := range right.branches() {
			result.append(appendDatatypeBooleanAtoms(first, second))
		}
	}
	return result
}
