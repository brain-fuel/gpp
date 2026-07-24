package smt

type integerAffineReal struct {
	integer Term[IntSort]
	offset  Rational
}

func decomposeIntegerAffineReal(term Term[RealSort]) (integerAffineReal, bool) {
	switch value := term.(type) {
	case Real:
		return integerAffineReal{offset: value.Value}, true
	case integerToReal:
		return integerAffineReal{integer: value.value}, true
	case RealAdd:
		result := integerAffineReal{}
		for _, item := range value.Values {
			next, ok := decomposeIntegerAffineReal(item)
			if !ok {
				return integerAffineReal{}, false
			}
			result.integer = addAffineIntegerTerms(result.integer, next.integer)
			result.offset = AddRational(result.offset, next.offset)
		}
		return result, true
	case RealSubtract:
		left, leftOK := decomposeIntegerAffineReal(value.Left)
		right, rightOK := decomposeIntegerAffineReal(value.Right)
		if !leftOK || !rightOK {
			return integerAffineReal{}, false
		}
		left.integer = subtractAffineIntegerTerms(left.integer, right.integer)
		left.offset = SubtractRational(left.offset, right.offset)
		return left, true
	case RealScale:
		if !value.Coefficient.IsInteger() {
			return integerAffineReal{}, false
		}
		item, ok := decomposeIntegerAffineReal(value.Value)
		if !ok {
			return integerAffineReal{}, false
		}
		coefficient := FloorRational(value.Coefficient)
		if item.integer != nil {
			item.integer = ScaleInteger(coefficient, item.integer)
		}
		item.offset = MultiplyRational(value.Coefficient, item.offset)
		return item, true
	default:
		return integerAffineReal{}, false
	}
}

func addAffineIntegerTerms(left, right Term[IntSort]) Term[IntSort] {
	if left == nil {
		return right
	}
	if right == nil {
		return left
	}
	return Add{Values: []Term[IntSort]{left, right}}
}

func subtractAffineIntegerTerms(left, right Term[IntSort]) Term[IntSort] {
	if right == nil {
		return left
	}
	if left == nil {
		return ScaleInteger(NewIntegerValue(-1), right)
	}
	return Subtract{Left: left, Right: right}
}

func floorIntegerAffineReal(term Term[RealSort]) (Term[IntSort], bool) {
	value, ok := decomposeIntegerAffineReal(term)
	if !ok || value.integer == nil {
		return nil, false
	}
	offset := FloorRational(value.offset)
	if CompareIntegerValue(offset, IntegerValue{}) == 0 {
		return value.integer, true
	}
	return addAffineIntegerTerms(value.integer, IntegerTerm(offset)), true
}

func integerAffineRealIsIntegral(term Term[RealSort]) (bool, bool) {
	value, ok := decomposeIntegerAffineReal(term)
	if !ok || value.integer == nil {
		return false, false
	}
	return value.offset.IsInteger(), true
}

func rationalScaledIntegerReal(
	term Term[RealSort],
) (Term[IntSort], IntegerValue, bool) {
	scale, ok := term.(RealScale)
	if !ok {
		return nil, IntegerValue{}, false
	}
	value, valueOK := decomposeIntegerAffineReal(scale.Value)
	if !valueOK || value.integer == nil || value.offset.Sign() != 0 {
		return nil, IntegerValue{}, false
	}
	numerator := RationalNumerator(scale.Coefficient)
	denominator := RationalDenominator(scale.Coefficient)
	return ScaleInteger(numerator, value.integer), denominator, true
}

func floorRationalScaledIntegerReal(term Term[RealSort]) (Term[IntSort], bool) {
	numerator, denominator, ok := rationalScaledIntegerReal(term)
	if !ok {
		return nil, false
	}
	return DivInteger(numerator, denominator), true
}

func rationalScaledIntegerRealIsIntegral(
	term Term[RealSort],
) (Term[BoolSort], bool) {
	numerator, denominator, ok := rationalScaledIntegerReal(term)
	if !ok {
		return nil, false
	}
	return Equal{
		Left:  ModInteger(numerator, denominator),
		Right: Integer{Value: 0},
	}, true
}

// rewriteSymbolicIntegerToReal lowers the complete conjunctive fragment in
// which symbolic to_real terms are compared with another to_real term or an
// exact rational constant. The resulting integer relations preserve SMT-LIB
// semantics exactly; unsupported mixed expressions are left untouched.
func rewriteSymbolicIntegerToReal(assertions []Term[BoolSort]) []Term[BoolSort] {
	var rewritten []Term[BoolSort]
	for index, assertion := range assertions {
		next, changed := rewriteSymbolicIntegerToRealAssertion(assertion)
		if !changed {
			if rewritten != nil {
				rewritten = append(rewritten, assertion)
			}
			continue
		}
		if rewritten == nil {
			rewritten = make([]Term[BoolSort], 0, len(assertions))
			rewritten = append(rewritten, assertions[:index]...)
		}
		rewritten = append(rewritten, next)
	}
	if rewritten == nil {
		return assertions
	}
	return rewritten
}

func rewriteSymbolicIntegerToRealAssertion(term Term[BoolSort]) (Term[BoolSort], bool) {
	switch value := term.(type) {
	case BooleanConjunction:
		terms := value.InlineTerms[:min(value.Count, len(value.InlineTerms))]
		negated := value.InlineNegated[:len(terms)]
		if value.OverflowTerms != nil {
			terms = value.OverflowTerms[:value.Count]
			negated = value.OverflowNegated[:value.Count]
		}
		var rewritten []Term[BoolSort]
		for index, item := range terms {
			next, changed := rewriteSymbolicIntegerToRealAssertion(item)
			if !changed {
				if rewritten != nil {
					if negated[index] {
						rewritten = append(rewritten, Not{Value: item})
					} else {
						rewritten = append(rewritten, item)
					}
				}
				continue
			}
			if rewritten == nil {
				rewritten = make([]Term[BoolSort], 0, len(terms))
				for previous := 0; previous < index; previous++ {
					if negated[previous] {
						rewritten = append(rewritten, Not{Value: terms[previous]})
					} else {
						rewritten = append(rewritten, terms[previous])
					}
				}
			}
			if negated[index] {
				next = Not{Value: next}
			}
			rewritten = append(rewritten, next)
		}
		if rewritten == nil {
			return term, false
		}
		return And{Values: rewritten}, true
	case And:
		var rewritten []Term[BoolSort]
		for index, item := range value.Values {
			next, changed := rewriteSymbolicIntegerToRealAssertion(item)
			if !changed {
				if rewritten != nil {
					rewritten = append(rewritten, item)
				}
				continue
			}
			if rewritten == nil {
				rewritten = make([]Term[BoolSort], 0, len(value.Values))
				rewritten = append(rewritten, value.Values[:index]...)
			}
			rewritten = append(rewritten, next)
		}
		if rewritten == nil {
			return term, false
		}
		return And{Values: rewritten}, true
	case Equal:
		left, leftOK := value.Left.(Term[RealSort])
		right, rightOK := value.Right.(Term[RealSort])
		if !leftOK || !rightOK {
			return term, false
		}
		return rewriteIntegerRealEquality(left, right)
	case RealLessEqual:
		return rewriteIntegerRealOrder(value.Left, value.Right, false)
	case RealLess:
		return rewriteIntegerRealOrder(value.Left, value.Right, true)
	case Not:
		rewritten, changed := rewriteSymbolicIntegerToRealAssertion(value.Value)
		if !changed {
			return term, false
		}
		return Not{Value: rewritten}, true
	default:
		return term, false
	}
}

func integerToRealSource(term Term[RealSort]) (Term[IntSort], bool) {
	value, ok := term.(integerToReal)
	return value.value, ok
}

func rewriteIntegerRealEquality(left, right Term[RealSort]) (Term[BoolSort], bool) {
	if relation, ok := rewriteAffineIntegerRealEquality(left, right); ok {
		return relation, true
	}
	leftInteger, leftOK := integerToRealSource(left)
	rightInteger, rightOK := integerToRealSource(right)
	switch {
	case leftOK && rightOK:
		return Equal{Left: leftInteger, Right: rightInteger}, true
	case leftOK:
		return integerEqualsRealConstant(leftInteger, right)
	case rightOK:
		return integerEqualsRealConstant(rightInteger, left)
	default:
		return nil, false
	}
}

func rewriteAffineIntegerRealEquality(left, right Term[RealSort]) (Term[BoolSort], bool) {
	difference, bound, ok := affineIntegerRealDifference(left, right)
	if !ok {
		return nil, false
	}
	if !bound.IsInteger() {
		return Bool{Value: false}, true
	}
	return Equal{Left: difference, Right: IntegerTerm(FloorRational(bound))}, true
}

func integerEqualsRealConstant(integer Term[IntSort], real Term[RealSort]) (Term[BoolSort], bool) {
	value, ok := ExactRealConstant(real)
	if !ok {
		return nil, false
	}
	if !value.IsInteger() {
		return Bool{Value: false}, true
	}
	return Equal{Left: integer, Right: IntegerTerm(FloorRational(value))}, true
}

func rewriteIntegerRealOrder(left, right Term[RealSort], strict bool) (Term[BoolSort], bool) {
	if relation, ok := rewriteAffineIntegerRealOrder(left, right, strict); ok {
		return relation, true
	}
	leftInteger, leftOK := integerToRealSource(left)
	rightInteger, rightOK := integerToRealSource(right)
	if leftOK && rightOK {
		if strict {
			return Less{Left: leftInteger, Right: rightInteger}, true
		}
		return LessEqual{Left: leftInteger, Right: rightInteger}, true
	}
	if leftOK {
		constant, ok := ExactRealConstant(right)
		if !ok {
			return nil, false
		}
		floor := FloorRational(constant)
		if strict && constant.IsInteger() {
			return Less{Left: leftInteger, Right: IntegerTerm(floor)}, true
		}
		return LessEqual{Left: leftInteger, Right: IntegerTerm(floor)}, true
	}
	if rightOK {
		constant, ok := ExactRealConstant(left)
		if !ok {
			return nil, false
		}
		floor := FloorRational(constant)
		if strict {
			return Less{Left: IntegerTerm(floor), Right: rightInteger}, true
		}
		ceiling := floor
		if !constant.IsInteger() {
			ceiling = AddIntegerValue(ceiling, NewIntegerValue(1))
		}
		return LessEqual{Left: IntegerTerm(ceiling), Right: rightInteger}, true
	}
	return nil, false
}

// affineIntegerRealDifference returns the integer-valued expression and exact
// rational bound for left <= right rewritten as integer <= bound.
func affineIntegerRealDifference(
	left, right Term[RealSort],
) (Term[IntSort], Rational, bool) {
	leftAffine, leftOK := decomposeIntegerAffineReal(left)
	rightAffine, rightOK := decomposeIntegerAffineReal(right)
	if !leftOK || !rightOK ||
		leftAffine.integer == nil && rightAffine.integer == nil {
		return nil, Rational{}, false
	}
	difference := subtractAffineIntegerTerms(leftAffine.integer, rightAffine.integer)
	if difference == nil {
		return nil, Rational{}, false
	}
	return difference, SubtractRational(rightAffine.offset, leftAffine.offset), true
}

func rewriteAffineIntegerRealOrder(
	left, right Term[RealSort],
	strict bool,
) (Term[BoolSort], bool) {
	difference, bound, ok := affineIntegerRealDifference(left, right)
	if !ok {
		return nil, false
	}
	floor := FloorRational(bound)
	if strict && bound.IsInteger() {
		return Less{Left: difference, Right: IntegerTerm(floor)}, true
	}
	return LessEqual{Left: difference, Right: IntegerTerm(floor)}, true
}
