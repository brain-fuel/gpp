package smt

type IntegerConditionalBranch struct {
	Application bool
	FunctionID  int
	ArgumentID  int
	Constant    IntegerValue
}

type IntegerConditionalComparison struct {
	Condition         IntegerDifferenceConstraint
	Then              IntegerConditionalBranch
	Else              IntegerConditionalBranch
	Bound             IntegerValue
	ApplicationOnLeft bool
	Strict            bool
}

type CompactConditionalIntegerEUFSystem struct {
	Base        CompactIntegerEUFSystem
	Conditional IntegerConditionalComparison
}

func (CompactConditionalIntegerEUFSystem) isTerm(BoolSort) {}

func solveCompactConditionalIntegerEUFSystem(
	system CompactConditionalIntegerEUFSystem,
) (checkOutcome, bool) {
	var unknown checkOutcome
	unknownSeen := false
	for branchIndex, branch := range [...]IntegerConditionalBranch{
		system.Conditional.Then, system.Conditional.Else,
	} {
		condition := system.Conditional.Condition
		if branchIndex == 1 {
			condition = negateIntegerDifferenceConstraint(condition)
		}
		var differenceTerms [12]Term[BoolSort]
		differenceCount := 0
		for _, constraint := range system.Base.differenceValues() {
			differenceTerms[differenceCount] = constraint
			differenceCount++
		}
		leftIDs, rightIDs := system.Base.equalityValues()
		for index := range leftIDs {
			for _, constraint := range [...]IntegerDifferenceConstraint{
				{
					PositiveID: leftIDs[index], NegativeID: rightIDs[index],
					HasPositive: true, HasNegative: true,
				},
				{
					PositiveID: rightIDs[index], NegativeID: leftIDs[index],
					HasPositive: true, HasNegative: true,
				},
			} {
				if differenceCount == len(differenceTerms) {
					return checkOutcome{}, false
				}
				differenceTerms[differenceCount] = constraint
				differenceCount++
			}
		}
		if differenceCount == len(differenceTerms) {
			return checkOutcome{}, false
		}
		differenceTerms[differenceCount] = condition
		differenceCount++
		differenceOutcome, recognized :=
			solveDifferenceAssertions(differenceTerms[:differenceCount])
		if !recognized {
			return checkOutcome{}, false
		}
		if differenceOutcome.status == checkUnsat {
			continue
		}
		if !branch.Application {
			if !integerConditionalConstantComparison(
				branch.Constant, system.Conditional,
			) {
				continue
			}
			outcome, recognized := solveCompactIntegerEUFSystem(system.Base)
			if !recognized {
				return checkOutcome{}, false
			}
			if outcome.status == checkSat {
				outcome.integers = differenceOutcome.integers
				return outcome, true
			}
			if outcome.status == checkUnknown {
				unknown, unknownSeen = outcome, true
			}
			continue
		}
		selected := system.Base
		comparison := IntegerUnaryComparison{
			FunctionID: branch.FunctionID, ArgumentID: branch.ArgumentID,
			Bound:             system.Conditional.Bound,
			ApplicationOnLeft: system.Conditional.ApplicationOnLeft,
			Strict:            system.Conditional.Strict,
		}
		if selected.UnaryComparisonCount >= len(selected.UnaryComparisons) ||
			selected.OverflowUnaryComparisons != nil {
			return checkOutcome{}, false
		}
		selected.UnaryComparisons[selected.UnaryComparisonCount] = comparison
		selected.UnaryComparisonCount++
		outcome, recognized := solveCompactIntegerEUFSystem(selected)
		if !recognized {
			return checkOutcome{}, false
		}
		if outcome.status == checkSat {
			outcome.integers = differenceOutcome.integers
			return outcome, true
		}
		if outcome.status == checkUnknown {
			unknown, unknownSeen = outcome, true
		}
	}
	if unknownSeen {
		return unknown, true
	}
	return checkOutcome{status: checkUnsat}, true
}

func negateIntegerDifferenceConstraint(
	value IntegerDifferenceConstraint,
) IntegerDifferenceConstraint {
	bound := NewIntegerValue(value.Bound)
	if value.Wide {
		bound = value.WideBound
	}
	bound = NegateIntegerValue(bound)
	result := IntegerDifferenceConstraint{
		PositiveID: value.NegativeID, NegativeID: value.PositiveID,
		HasPositive: value.HasNegative, HasNegative: value.HasPositive,
		Strict: !value.Strict,
	}
	if projected, ok := bound.Int64(); ok {
		result.Bound = projected
	} else {
		result.Wide, result.WideBound = true, bound
	}
	return result
}

func integerConditionalConstantComparison(
	value IntegerValue, comparison IntegerConditionalComparison,
) bool {
	order := CompareIntegerValue(value, comparison.Bound)
	if comparison.ApplicationOnLeft {
		if comparison.Strict {
			return order < 0
		}
		return order <= 0
	}
	if comparison.Strict {
		return order > 0
	}
	return order >= 0
}

// solveSharedIntegerConditionalEUF eliminates integer-valued conditionals by
// exact case splitting. Each branch retains the condition (or its logical
// complement), so applications in either arm are purified only under the
// branch in which they are selected.
func solveSharedIntegerConditionalEUF(
	assertions []Term[BoolSort],
) (checkOutcome, bool) {
	for assertionIndex, assertion := range assertions {
		thenAssertion, elseAssertion, condition, found, ok :=
			splitSharedIntegerConditionalAssertion(assertion)
		if !ok {
			return checkOutcome{}, false
		}
		if !found {
			continue
		}
		var unknown checkOutcome
		unknownSeen := false
		for _, branch := range []struct {
			assertion Term[BoolSort]
			condition Term[BoolSort]
		}{
			{thenAssertion, conditionalPolarity(condition, true)},
			{elseAssertion, conditionalPolarity(condition, false)},
		} {
			rewritten := make([]Term[BoolSort], len(assertions)+1)
			copy(rewritten, assertions)
			rewritten[assertionIndex] = branch.assertion
			rewritten[len(assertions)] = branch.condition
			outcome, recognized := solveSharedIntegerConditionalEUF(rewritten)
			if !recognized {
				outcome, recognized = solveSharedIntegerEUF(rewritten)
			}
			if !recognized {
				return checkOutcome{}, false
			}
			if outcome.status == checkSat {
				return outcome, true
			}
			if outcome.status == checkUnknown {
				unknown, unknownSeen = outcome, true
			}
		}
		if unknownSeen {
			return unknown, true
		}
		return checkOutcome{status: checkUnsat}, true
	}
	return checkOutcome{}, false
}

func conditionalPolarity(
	condition Term[BoolSort], positive bool,
) Term[BoolSort] {
	if positive {
		return condition
	}
	switch value := condition.(type) {
	case Bool:
		return Bool{Value: !value.Value}
	case Not:
		return value.Value
	case LessEqual:
		return Less{Left: value.Right, Right: value.Left}
	case Less:
		return LessEqual{Left: value.Right, Right: value.Left}
	case IntegerDifferenceConstraint:
		return conditionalPolarity(integerDifferenceAsTerm(value), false)
	default:
		return Not{Value: condition}
	}
}

func splitSharedIntegerConditionalAssertion(
	assertion Term[BoolSort],
) (Term[BoolSort], Term[BoolSort], Term[BoolSort], bool, bool) {
	switch value := assertion.(type) {
	case And:
		for index, item := range value.Values {
			thenItem, elseItem, condition, found, ok :=
				splitSharedIntegerConditionalAssertion(item)
			if !ok || !found {
				if !ok {
					return nil, nil, nil, false, false
				}
				continue
			}
			thenItems := append([]Term[BoolSort](nil), value.Values...)
			elseItems := append([]Term[BoolSort](nil), value.Values...)
			thenItems[index], elseItems[index] = thenItem, elseItem
			return And{Values: thenItems}, And{Values: elseItems},
				condition, true, true
		}
	case BooleanConjunction:
		items, polarities := value.values()
		for index, item := range items {
			thenItem, elseItem, condition, found, ok :=
				splitSharedIntegerConditionalAssertion(item)
			if !ok || !found {
				if !ok {
					return nil, nil, nil, false, false
				}
				continue
			}
			thenItems := make([]Term[BoolSort], len(items))
			elseItems := make([]Term[BoolSort], len(items))
			for itemIndex, original := range items {
				thenItems[itemIndex], elseItems[itemIndex] = original, original
				if polarities[itemIndex] {
					thenItems[itemIndex] = Not{Value: original}
					elseItems[itemIndex] = Not{Value: original}
				}
			}
			if polarities[index] {
				thenItem = Not{Value: thenItem}
				elseItem = Not{Value: elseItem}
			}
			thenItems[index], elseItems[index] = thenItem, elseItem
			return And{Values: thenItems}, And{Values: elseItems},
				condition, true, true
		}
	case Not:
		thenItem, elseItem, condition, found, ok :=
			splitSharedIntegerConditionalAssertion(value.Value)
		if found {
			return Not{Value: thenItem}, Not{Value: elseItem},
				condition, true, ok
		}
		return nil, nil, nil, false, ok
	case LessEqual:
		return splitConditionalIntegerRelation(value.Left, value.Right,
			func(left, right Term[IntSort]) Term[BoolSort] {
				return LessEqual{Left: left, Right: right}
			})
	case Less:
		return splitConditionalIntegerRelation(value.Left, value.Right,
			func(left, right Term[IntSort]) Term[BoolSort] {
				return Less{Left: left, Right: right}
			})
	case Equal:
		left, leftOK := value.Left.(Term[IntSort])
		right, rightOK := value.Right.(Term[IntSort])
		if !leftOK || !rightOK {
			return nil, nil, nil, false, true
		}
		return splitConditionalIntegerRelation(left, right,
			func(left, right Term[IntSort]) Term[BoolSort] {
				return Equal{Left: left, Right: right}
			})
	}
	return nil, nil, nil, false, true
}

func splitConditionalIntegerRelation(
	left, right Term[IntSort],
	build func(Term[IntSort], Term[IntSort]) Term[BoolSort],
) (Term[BoolSort], Term[BoolSort], Term[BoolSort], bool, bool) {
	thenLeft, elseLeft, condition, found, ok :=
		splitConditionalIntegerTerm(left)
	if !ok {
		return nil, nil, nil, false, false
	}
	if found {
		return build(thenLeft, right), build(elseLeft, right),
			condition, true, true
	}
	thenRight, elseRight, condition, found, ok :=
		splitConditionalIntegerTerm(right)
	if !ok || !found {
		return nil, nil, nil, false, ok
	}
	return build(left, thenRight), build(left, elseRight),
		condition, true, true
}

func splitConditionalIntegerTerm(
	term Term[IntSort],
) (Term[IntSort], Term[IntSort], Term[BoolSort], bool, bool) {
	switch value := term.(type) {
	case If[IntSort]:
		return value.Then, value.Else, value.Condition, true, true
	case Add:
		for index, item := range value.Values {
			thenItem, elseItem, condition, found, ok :=
				splitConditionalIntegerTerm(item)
			if !ok || !found {
				if !ok {
					return nil, nil, nil, false, false
				}
				continue
			}
			thenItems := append([]Term[IntSort](nil), value.Values...)
			elseItems := append([]Term[IntSort](nil), value.Values...)
			thenItems[index], elseItems[index] = thenItem, elseItem
			return Add{Values: thenItems}, Add{Values: elseItems},
				condition, true, true
		}
	case Subtract:
		thenItem, elseItem, condition, found, ok :=
			splitConditionalIntegerTerm(value.Left)
		if found {
			return Subtract{Left: thenItem, Right: value.Right},
				Subtract{Left: elseItem, Right: value.Right},
				condition, true, ok
		}
		thenItem, elseItem, condition, found, ok =
			splitConditionalIntegerTerm(value.Right)
		if found {
			return Subtract{Left: value.Left, Right: thenItem},
				Subtract{Left: value.Left, Right: elseItem},
				condition, true, ok
		}
		return nil, nil, nil, false, ok
	case IntegerScale:
		thenItem, elseItem, condition, found, ok :=
			splitConditionalIntegerTerm(value.Value)
		if found {
			return IntegerScale{Coefficient: value.Coefficient, Value: thenItem},
				IntegerScale{Coefficient: value.Coefficient, Value: elseItem},
				condition, true, ok
		}
		return nil, nil, nil, false, ok
	case sortedUnaryApplication[IntSort]:
		argument, ok := value.argument.(Term[IntSort])
		if !ok {
			return nil, nil, nil, false, false
		}
		thenArgument, elseArgument, condition, found, ok :=
			splitConditionalIntegerTerm(argument)
		if !found {
			return nil, nil, nil, false, ok
		}
		function, ok := value.function.(SortedUnaryFunction[IntSort, IntSort])
		if !ok {
			return nil, nil, nil, false, false
		}
		return ApplySortedUnary(function, thenArgument),
			ApplySortedUnary(function, elseArgument), condition, true, true
	case sortedBinaryApplication[IntSort]:
		function, functionOK := value.function.(SortedBinaryFunction[IntSort, IntSort, IntSort])
		first, firstOK := value.first.(Term[IntSort])
		second, secondOK := value.second.(Term[IntSort])
		if !functionOK || !firstOK || !secondOK {
			return nil, nil, nil, false, false
		}
		thenItem, elseItem, condition, found, ok :=
			splitConditionalIntegerTerm(first)
		if found {
			return ApplySortedBinary(function, thenItem, second),
				ApplySortedBinary(function, elseItem, second),
				condition, true, ok
		}
		thenItem, elseItem, condition, found, ok =
			splitConditionalIntegerTerm(second)
		if found {
			return ApplySortedBinary(function, first, thenItem),
				ApplySortedBinary(function, first, elseItem),
				condition, true, ok
		}
		return nil, nil, nil, false, ok
	case sortedTernaryApplication[IntSort]:
		function, functionOK := value.function.(SortedTernaryFunction[IntSort, IntSort, IntSort, IntSort])
		first, firstOK := value.first.(Term[IntSort])
		second, secondOK := value.second.(Term[IntSort])
		third, thirdOK := value.third.(Term[IntSort])
		if !functionOK || !firstOK || !secondOK || !thirdOK {
			return nil, nil, nil, false, false
		}
		thenItem, elseItem, condition, found, ok :=
			splitConditionalIntegerTerm(first)
		if found {
			return ApplySortedTernary(function, thenItem, second, third),
				ApplySortedTernary(function, elseItem, second, third),
				condition, true, ok
		}
		thenItem, elseItem, condition, found, ok =
			splitConditionalIntegerTerm(second)
		if found {
			return ApplySortedTernary(function, first, thenItem, third),
				ApplySortedTernary(function, first, elseItem, third),
				condition, true, ok
		}
		thenItem, elseItem, condition, found, ok =
			splitConditionalIntegerTerm(third)
		if found {
			return ApplySortedTernary(function, first, second, thenItem),
				ApplySortedTernary(function, first, second, elseItem),
				condition, true, ok
		}
		return nil, nil, nil, false, ok
	}
	return nil, nil, nil, false, true
}
