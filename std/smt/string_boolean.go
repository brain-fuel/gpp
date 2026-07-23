package smt

func containsBooleanStringAssertions(assertions []Term[BoolSort]) bool {
	for _, assertion := range assertions {
		if containsBooleanString(assertion) {
			return true
		}
	}
	return false
}

func containsBooleanString(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case Or, Implies, Iff, If[BoolSort]:
		return containsStringTheory(term)
	case Not:
		return containsBooleanString(value.Value)
	case And:
		for _, item := range value.Values {
			if containsBooleanString(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsBooleanString(item) {
				return true
			}
		}
	case Equal:
		left, leftOK := value.Left.(Term[BoolSort])
		right, rightOK := value.Right.(Term[BoolSort])
		return leftOK && rightOK && (containsStringTheory(left) || containsStringTheory(right))
	}
	return false
}

func solveBooleanStringAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	branches := datatypeBooleanBranches{}
	branches.append(datatypeBooleanBranch{})
	for _, assertion := range assertions {
		next, ok := normalizeStringBoolean(assertion, true)
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
		outcome, recognized := solveStringAssertions(branch.atoms())
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

func normalizeStringBoolean(term Term[BoolSort], positive bool) (datatypeBooleanBranches, bool) {
	switch value := term.(type) {
	case Bool:
		if value.Value == positive {
			result := datatypeBooleanBranches{}
			result.append(datatypeBooleanBranch{})
			return result, true
		}
		return datatypeBooleanBranches{}, true
	case Not:
		return normalizeStringBoolean(value.Value, !positive)
	case And:
		return normalizeStringBooleanMany(value.Values, positive, positive)
	case Or:
		return normalizeStringBooleanMany(value.Values, positive, !positive)
	case Implies:
		if positive {
			left, leftOK := normalizeStringBoolean(value.Left, false)
			right, rightOK := normalizeStringBoolean(value.Right, true)
			return unionDatatypeBooleanBranches(left, right), leftOK && rightOK
		}
		left, leftOK := normalizeStringBoolean(value.Left, true)
		right, rightOK := normalizeStringBoolean(value.Right, false)
		return combineDatatypeBooleanBranches(left, right), leftOK && rightOK
	case Iff:
		return normalizeStringEquivalence(value.Left, value.Right, positive)
	case If[BoolSort]:
		conditionTrue, firstOK := normalizeStringBoolean(value.Condition, true)
		conditionFalse, secondOK := normalizeStringBoolean(value.Condition, false)
		thenBranch, thirdOK := normalizeStringBoolean(value.Then, positive)
		elseBranch, fourthOK := normalizeStringBoolean(value.Else, positive)
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
			part, ok := normalizeStringBoolean(item, positive != negated[index])
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
			return normalizeStringEquivalence(left, right, positive)
		}
		return stringBooleanAtom(term, positive)
	default:
		return stringBooleanAtom(term, positive)
	}
}

func normalizeStringEquivalence(left, right Term[BoolSort], positive bool) (datatypeBooleanBranches, bool) {
	leftTrue, firstOK := normalizeStringBoolean(left, true)
	rightTrue, secondOK := normalizeStringBoolean(right, true)
	leftFalse, thirdOK := normalizeStringBoolean(left, false)
	rightFalse, fourthOK := normalizeStringBoolean(right, false)
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

func normalizeStringBooleanMany(terms []Term[BoolSort], childPositive, conjunction bool) (datatypeBooleanBranches, bool) {
	result := datatypeBooleanBranches{}
	if conjunction {
		result.append(datatypeBooleanBranch{})
	}
	for _, term := range terms {
		part, ok := normalizeStringBoolean(term, childPositive)
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

func stringBooleanAtom(term Term[BoolSort], positive bool) (datatypeBooleanBranches, bool) {
	if !containsStringTheory(term) {
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
