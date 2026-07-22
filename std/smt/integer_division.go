package smt

import "math"

type IntegerDivModRelation struct {
	SymbolID  int
	Divisor   IntegerValue
	Expected  IntegerValue
	Remainder bool
}

func (IntegerDivModRelation) isTerm(BoolSort) {}

type IntegerDivModSystem struct {
	EqualityCount int
	RelationCount int
	Equalities    [4]IntegerLinearEquality
	Relations     [4]IntegerDivModRelation
}

func (IntegerDivModSystem) isTerm(BoolSort) {}

func CompactIntegerDivModEquality(left, right Term[IntSort]) (IntegerDivModRelation, bool) {
	expected, ok := exactIntegerConstant(right)
	if !ok {
		return IntegerDivModRelation{}, false
	}
	switch value := left.(type) {
	case IntegerDiv:
		id, symbol := IntegerVariableID(value.Dividend)
		return IntegerDivModRelation{SymbolID: id, Divisor: value.Divisor, Expected: expected}, symbol && CompareIntegerValue(value.Divisor, IntegerValue{}) > 0
	case IntegerMod:
		id, symbol := IntegerVariableID(value.Dividend)
		return IntegerDivModRelation{SymbolID: id, Divisor: value.Divisor, Expected: expected, Remainder: true}, symbol && CompareIntegerValue(value.Divisor, IntegerValue{}) > 0
	}
	return IntegerDivModRelation{}, false
}

type compactDivModSymbol struct {
	id       int
	assigned bool
	value    IntegerValue
}

func solveCompactIntegerDivModAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	if len(assertions) == 1 {
		if system, ok := assertions[0].(IntegerDivModSystem); ok {
			return solveCompactIntegerDivModValues(system.Equalities[:system.EqualityCount], system.Relations[:system.RelationCount])
		}
	}
	var terms [8]Term[BoolSort]
	count := 0
	var flatten func(Term[BoolSort]) bool
	flatten = func(term Term[BoolSort]) bool {
		switch value := term.(type) {
		case And:
			for _, item := range value.Values {
				if !flatten(item) {
					return false
				}
			}
			return true
		case BooleanConjunction:
			values, negated := value.values()
			for index, item := range values {
				if negated[index] || !flatten(item) {
					return false
				}
			}
			return true
		case IntegerLinearEquality, IntegerDivModRelation:
			if count == len(terms) {
				return false
			}
			terms[count], count = term, count+1
			return true
		default:
			return false
		}
	}
	for _, assertion := range assertions {
		if !flatten(assertion) {
			return checkOutcome{}, false
		}
	}
	if count == 0 {
		return checkOutcome{}, false
	}
	var equalities [8]IntegerLinearEquality
	var relations [8]IntegerDivModRelation
	equalityCount, relationCount := 0, 0
	for _, term := range terms[:count] {
		switch value := term.(type) {
		case IntegerLinearEquality:
			equalities[equalityCount] = value
			equalityCount++
		case IntegerDivModRelation:
			relations[relationCount] = value
			relationCount++
		}
	}
	return solveCompactIntegerDivModValues(equalities[:equalityCount], relations[:relationCount])
}

func solveCompactIntegerDivModValues(equalities []IntegerLinearEquality, relations []IntegerDivModRelation) (checkOutcome, bool) {
	var symbols [4]compactDivModSymbol
	symbolCount := 0
	find := func(id int) *compactDivModSymbol {
		for index := 0; index < symbolCount; index++ {
			if symbols[index].id == id {
				return &symbols[index]
			}
		}
		if symbolCount == len(symbols) {
			return nil
		}
		symbols[symbolCount].id = id
		symbolCount++
		return &symbols[symbolCount-1]
	}
	for _, equality := range equalities {
		symbol := find(equality.ID)
		if symbol == nil {
			return checkOutcome{}, false
		}
		numerator, denominator := equality.Value, NewIntegerValue(equality.Coefficient)
		if equality.Coefficient < 0 {
			numerator, denominator = NegateIntegerValue(numerator), NegateIntegerValue(denominator)
		}
		quotient, remainder, valid := DivModIntegerValue(numerator, denominator)
		if !valid || CompareIntegerValue(remainder, IntegerValue{}) != 0 {
			return checkOutcome{status: checkUnsat}, true
		}
		if symbol.assigned && CompareIntegerValue(symbol.value, quotient) != 0 {
			return checkOutcome{status: checkUnsat}, true
		}
		symbol.assigned, symbol.value = true, quotient
	}
	if len(relations) == 0 {
		return checkOutcome{}, false
	}
	for _, relation := range relations {
		symbol := find(relation.SymbolID)
		if symbol == nil || !symbol.assigned {
			return checkOutcome{}, false
		}
		quotient, remainder, valid := DivModIntegerValue(symbol.value, relation.Divisor)
		actual := quotient
		if relation.Remainder {
			actual = remainder
		}
		if !valid || CompareIntegerValue(actual, relation.Expected) != 0 {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	model := integerModel{}
	for _, symbol := range symbols[:symbolCount] {
		if symbol.assigned {
			model.set(symbol.id, symbol.value)
		}
	}
	return checkOutcome{status: checkSat, integers: model}, true
}

type integerDivisionEliminator struct {
	nextID      int
	definitions []Term[BoolSort]
}

func containsIntegerDivision(term any) bool {
	switch value := term.(type) {
	case IntegerDiv, IntegerMod:
		return true
	case IntegerScale:
		return containsIntegerDivision(value.Value)
	case Add:
		for _, item := range value.Values {
			if containsIntegerDivision(item) {
				return true
			}
		}
	case Subtract:
		return containsIntegerDivision(value.Left) || containsIntegerDivision(value.Right)
	case Equal:
		return containsIntegerDivision(value.Left) || containsIntegerDivision(value.Right)
	case LessEqual:
		return containsIntegerDivision(value.Left) || containsIntegerDivision(value.Right)
	case Less:
		return containsIntegerDivision(value.Left) || containsIntegerDivision(value.Right)
	case And:
		for _, item := range value.Values {
			if containsIntegerDivision(item) {
				return true
			}
		}
	case Or:
		for _, item := range value.Values {
			if containsIntegerDivision(item) {
				return true
			}
		}
	case Not:
		return containsIntegerDivision(value.Value)
	case Implies:
		return containsIntegerDivision(value.Left) || containsIntegerDivision(value.Right)
	case Iff:
		return containsIntegerDivision(value.Left) || containsIntegerDivision(value.Right)
	case BooleanConjunction:
		terms, _ := value.values()
		for _, item := range terms {
			if containsIntegerDivision(item) {
				return true
			}
		}
	}
	return false
}

func eliminateIntegerDivision(assertions []Term[BoolSort]) ([]Term[BoolSort], bool, bool) {
	changed := false
	maximum := -1
	for _, assertion := range assertions {
		changed = changed || containsIntegerDivision(assertion)
		collectTheoryIntegerIDs(assertion, func(id int) {
			if id > maximum {
				maximum = id
			}
		})
	}
	if !changed {
		return assertions, false, true
	}
	if maximum == math.MaxInt {
		return nil, true, false
	}
	eliminator := integerDivisionEliminator{nextID: maximum + 1}
	rewritten := make([]Term[BoolSort], 0, len(assertions)+6)
	for _, assertion := range assertions {
		term, ok := eliminator.boolean(assertion)
		if !ok {
			return nil, true, false
		}
		rewritten = append(rewritten, term)
	}
	rewritten = append(rewritten, eliminator.definitions...)
	return rewritten, true, true
}

func (eliminator *integerDivisionEliminator) boolean(term Term[BoolSort]) (Term[BoolSort], bool) {
	switch value := term.(type) {
	case Bool, IntegerDifferenceConstraint, IntegerDifferenceSystem, IntegerLinearEquality, IntegerLinearDisequality, IntegerLinearChoice, integerLinearStrictBound:
		return term, true
	case LessEqual:
		left, leftOK := eliminator.integer(value.Left)
		right, rightOK := eliminator.integer(value.Right)
		return LessEqual{Left: left, Right: right}, leftOK && rightOK
	case Less:
		left, leftOK := eliminator.integer(value.Left)
		right, rightOK := eliminator.integer(value.Right)
		return Less{Left: left, Right: right}, leftOK && rightOK
	case Equal:
		left, leftOK := value.Left.(Term[IntSort])
		right, rightOK := value.Right.(Term[IntSort])
		if !leftOK || !rightOK {
			return term, false
		}
		left, leftOK = eliminator.integer(left)
		right, rightOK = eliminator.integer(right)
		return Equal{Left: left, Right: right}, leftOK && rightOK
	case And:
		values := make([]Term[BoolSort], len(value.Values))
		for index, item := range value.Values {
			converted, ok := eliminator.boolean(item)
			if !ok {
				return term, false
			}
			values[index] = converted
		}
		return And{Values: values}, true
	case Or:
		values := make([]Term[BoolSort], len(value.Values))
		for index, item := range value.Values {
			converted, ok := eliminator.boolean(item)
			if !ok {
				return term, false
			}
			values[index] = converted
		}
		return Or{Values: values}, true
	case Not:
		converted, ok := eliminator.boolean(value.Value)
		return Not{Value: converted}, ok
	case Implies:
		left, leftOK := eliminator.boolean(value.Left)
		right, rightOK := eliminator.boolean(value.Right)
		return Implies{Left: left, Right: right}, leftOK && rightOK
	case Iff:
		left, leftOK := eliminator.boolean(value.Left)
		right, rightOK := eliminator.boolean(value.Right)
		return Iff{Left: left, Right: right}, leftOK && rightOK
	case BooleanConjunction:
		terms, negated := value.values()
		converted := BooleanConjunction{Count: len(terms)}
		if len(terms) > len(converted.InlineTerms) {
			converted.OverflowTerms = make([]Term[BoolSort], len(terms))
			converted.OverflowNegated = append([]bool(nil), negated...)
		}
		for index, item := range terms {
			next, ok := eliminator.boolean(item)
			if !ok {
				return term, false
			}
			if converted.OverflowTerms != nil {
				converted.OverflowTerms[index] = next
			} else {
				converted.InlineTerms[index], converted.InlineNegated[index] = next, negated[index]
			}
		}
		return converted, true
	default:
		return term, false
	}
}

func (eliminator *integerDivisionEliminator) integer(term Term[IntSort]) (Term[IntSort], bool) {
	switch value := term.(type) {
	case Integer, integerExact[IntSort], IntSymbol, integerVariable[IntSort]:
		return term, true
	case Add:
		values := make([]Term[IntSort], len(value.Values))
		for index, item := range value.Values {
			converted, ok := eliminator.integer(item)
			if !ok {
				return term, false
			}
			values[index] = converted
		}
		return Add{Values: values}, true
	case Subtract:
		left, leftOK := eliminator.integer(value.Left)
		right, rightOK := eliminator.integer(value.Right)
		return Subtract{Left: left, Right: right}, leftOK && rightOK
	case IntegerScale:
		converted, ok := eliminator.integer(value.Value)
		return IntegerScale{Coefficient: value.Coefficient, Value: converted}, ok
	case IntegerDiv:
		return eliminator.division(value.Dividend, value.Divisor, false)
	case IntegerMod:
		return eliminator.division(value.Dividend, value.Divisor, true)
	default:
		return term, false
	}
}

func (eliminator *integerDivisionEliminator) division(dividend Term[IntSort], divisor IntegerValue, remainderResult bool) (Term[IntSort], bool) {
	if CompareIntegerValue(divisor, IntegerValue{}) <= 0 || eliminator.nextID > math.MaxInt-1 {
		return nil, false
	}
	converted, ok := eliminator.integer(dividend)
	if !ok {
		return nil, false
	}
	quotientID, remainderID := eliminator.nextID, eliminator.nextID+1
	eliminator.nextID += 2
	quotient, remainder := IntegerVariable(quotientID), IntegerVariable(remainderID)
	decomposition := Equal{Left: converted, Right: Add{Values: []Term[IntSort]{ScaleInteger(divisor, quotient), remainder}}}
	eliminator.definitions = append(eliminator.definitions,
		decomposition,
		LessEqual{Left: Integer{Value: 0}, Right: remainder},
		Less{Left: remainder, Right: IntegerTerm(divisor)},
	)
	if remainderResult {
		return remainder, true
	}
	return quotient, true
}
