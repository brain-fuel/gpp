package smtlib

import (
	"strconv"
	"strings"

	smt "goforge.dev/goplus/std/smt"
)

const (
	fpFastAcknowledge uint8 = iota + 1
	fpFastDeclare
	fpFastAssign
	fpFastRound
	fpFastMinMax
	fpFastAdd
	fpFastSub
	fpFastMul
	fpFastDiv
	fpFastFMA
	fpFastSqrt
	fpFastRem
	fpFastConvert
	fpFastFromBV
	fpFastFormat
	fpFastToReal
	fpFastToRealAffine
	fpFastLinearReal
	fpFastPredicate
	fpFastComparison
	fpFastEquality
	fpFastGroundEquality
	fpFastCheck
)

type fpFastCommand struct {
	kind                          uint8
	symbolID, secondSymbolID      int
	thirdSymbolID                 int
	exponentBits                  int
	significandBits, commandIndex int
	sourceExponentBits            int
	sourceSignificandBits         int
	name, secondName              string
	value                         smt.BitVectorValue
	realValue                     smt.Rational
	mode                          smt.FloatingPointRoundingMode
	predicate                     uint8
	comparison                    uint8
	operation                     uint8
	width                         int
	signed                        bool
	negated                       bool
	groundHolds                   bool
	realTermCount                 int
	realTerms                     [4]smt.FloatingPointToRealTerm
	ordinaryRealTermCount         int
	ordinaryRealTerms             [4]smt.FloatingPointToRealRealTerm
}

type fpFastSymbol struct {
	name             string
	id, exponentBits int
	significandBits  int
	bitWidth         int
	real             bool
}

type fpFastToken struct {
	kind       uint8
	start, end int
}

const (
	fpFastAtom uint8 = iota + 1
	fpFastLeft
	fpFastRight
)

type fpFastScanner struct {
	source string
	at     int
}

type fpFastOperand struct {
	kind                   uint8
	symbolID, exponentBits int
	significandBits        int
	sourceExponentBits     int
	sourceSignificandBits  int
	value                  smt.BitVectorValue
	realValue              smt.Rational
	mode                   smt.FloatingPointRoundingMode
	secondSymbolID         int
	thirdSymbolID          int
	operation              uint8
	width                  int
	signed                 bool
}

type fpFastRealAffine struct {
	count     int
	terms     [4]smt.FloatingPointToRealTerm
	realCount int
	realTerms [4]smt.FloatingPointToRealRealTerm
	constant  smt.Rational
}

func (value *fpFastRealAffine) accumulate(
	other fpFastRealAffine,
	multiplier smt.Rational,
) bool {
	value.constant = smt.AddRational(
		value.constant, smt.MultiplyRational(other.constant, multiplier),
	)
	for index := 0; index < other.count; index++ {
		term := other.terms[index]
		term.Coefficient = smt.MultiplyRational(term.Coefficient, multiplier)
		merged := false
		for existingIndex := 0; existingIndex < value.count; existingIndex++ {
			existing := &value.terms[existingIndex]
			if existing.ExponentBits == term.ExponentBits &&
				existing.SignificandBits == term.SignificandBits &&
				existing.SymbolID == term.SymbolID {
				existing.Coefficient = smt.AddRational(
					existing.Coefficient, term.Coefficient,
				)
				if existing.Coefficient.Sign() == 0 {
					copy(
						value.terms[existingIndex:],
						value.terms[existingIndex+1:value.count],
					)
					value.count--
				}
				merged = true
				break
			}
		}
		if !merged {
			if value.count == len(value.terms) {
				return false
			}
			value.terms[value.count] = term
			value.count++
		}
	}
	for index := 0; index < other.realCount; index++ {
		term := other.realTerms[index]
		term.Coefficient = smt.MultiplyRational(term.Coefficient, multiplier)
		merged := false
		for existingIndex := 0; existingIndex < value.realCount; existingIndex++ {
			existing := &value.realTerms[existingIndex]
			if existing.SymbolID == term.SymbolID {
				existing.Coefficient = smt.AddRational(
					existing.Coefficient, term.Coefficient,
				)
				if existing.Coefficient.Sign() == 0 {
					copy(
						value.realTerms[existingIndex:],
						value.realTerms[existingIndex+1:value.realCount],
					)
					value.realCount--
				}
				merged = true
				break
			}
		}
		if !merged {
			if value.realCount == len(value.realTerms) {
				return false
			}
			value.realTerms[value.realCount] = term
			value.realCount++
		}
	}
	return true
}

func fpFastNegateLinearReal(constraint *smt.LinearRealConstraint) {
	constraint.Constant = smt.NegateRational(constraint.Constant)
	for index := 0; index < constraint.Count; index++ {
		constraint.Coefficients[index] =
			smt.NegateRational(constraint.Coefficients[index])
	}
}

const (
	fpFastSymbolBits uint8 = iota + 1
	fpFastRoundedBits
	fpFastMinMaxBits
	fpFastAddBits
	fpFastSubBits
	fpFastMulBits
	fpFastDivBits
	fpFastFMABits
	fpFastSqrtBits
	fpFastRemBits
	fpFastConversionBits
	fpFastBitVectorSymbolBits
	fpFastFromBVBits
	fpFastFormatBits
	fpFastExactFloatingBits
	fpFastLiteralBits
	fpFastToRealValue
	fpFastRealLiteral
)

func executeFloatingPointFast(source string) (ExecutionResult, bool) {
	if !strings.Contains(source, "QF_FP") &&
		!strings.Contains(source, "fp.to_real") {
		return nil, false
	}
	var commands [32]fpFastCommand
	var symbols [16]fpFastSymbol
	commandCount, symbolCount := 0, 0
	scanner := fpFastScanner{source: source}
	for {
		token, ok := scanner.next()
		if !ok {
			break
		}
		if token.kind != fpFastLeft || commandCount == len(commands) {
			return nil, false
		}
		operator, ok := scanner.atom()
		if !ok {
			return nil, false
		}
		command := fpFastCommand{commandIndex: commandCount}
		switch scanner.text(operator) {
		case "set-logic":
			logic, logicOK := scanner.atom()
			if !logicOK ||
				(scanner.text(logic) != "QF_FP" &&
					scanner.text(logic) != "QF_FPBV" &&
					scanner.text(logic) != "ALL") ||
				!scanner.right() {
				return nil, false
			}
			command.kind = fpFastAcknowledge
		case "declare-const":
			name, nameOK := scanner.atom()
			if !nameOK || symbolCount == len(symbols) {
				return nil, false
			}
			nameText := scanner.text(name)
			sortSnapshot := scanner.at
			if sortToken, sortOK := scanner.atom(); sortOK &&
				scanner.text(sortToken) == "Real" && scanner.right() {
				for index := 0; index < symbolCount; index++ {
					if symbols[index].name == nameText {
						return nil, false
					}
				}
				symbolCount++
				symbols[symbolCount-1] = fpFastSymbol{
					name: nameText, id: symbolCount, real: true,
				}
				command.kind = fpFastDeclare
				command.symbolID, command.name = symbolCount, nameText
				break
			}
			scanner.at = sortSnapshot
			if !scanner.left() {
				return nil, false
			}
			marker, markerOK := scanner.atom()
			sort, sortOK := scanner.atom()
			first, firstOK := scanner.positiveInt()
			second, secondOK := 0, false
			if sortOK && scanner.text(sort) == "FloatingPoint" {
				second, secondOK = scanner.positiveInt()
			}
			floating := markerOK && sortOK && firstOK && secondOK &&
				scanner.text(marker) == "_" &&
				scanner.text(sort) == "FloatingPoint" &&
				first >= 2 && second >= 2
			bitVector := markerOK && sortOK && firstOK &&
				scanner.text(marker) == "_" &&
				scanner.text(sort) == "BitVec"
			if !floating && !bitVector ||
				!scanner.right() || !scanner.right() {
				return nil, false
			}
			for index := 0; index < symbolCount; index++ {
				if symbols[index].name == nameText {
					return nil, false
				}
			}
			symbolCount++
			symbols[symbolCount-1] = fpFastSymbol{
				name: nameText, id: symbolCount,
				exponentBits: first, significandBits: second,
			}
			if bitVector {
				symbols[symbolCount-1].exponentBits = 0
				symbols[symbolCount-1].bitWidth = first
			}
			command.kind = fpFastDeclare
			command.symbolID, command.name = symbolCount, nameText
			command.exponentBits, command.significandBits = first, second
			if bitVector {
				command.exponentBits, command.width = 0, first
			}
		case "assert":
			relation, relationOK := scanner.formula(symbols[:symbolCount])
			if !relationOK || !scanner.right() {
				return nil, false
			}
			command = relation
			command.commandIndex = commandCount
		case "check-sat":
			if !scanner.right() {
				return nil, false
			}
			command.kind = fpFastCheck
		default:
			return nil, false
		}
		commands[commandCount] = command
		commandCount++
	}
	if commandCount == 0 {
		return nil, false
	}
	responses := make([]Response, 0, commandCount)
	solver := smt.New()
	nextAssertion := 1
	groundUnsat := false
	for index := 0; index < commandCount; index++ {
		command := commands[index]
		switch command.kind {
		case fpFastAcknowledge, fpFastDeclare:
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastAssign:
			width := command.exponentBits + command.significandBits
			if command.width != 0 {
				width = command.width
			}
			relation := smt.BitVectorRelation{
				Width:    width,
				SymbolID: command.symbolID, Value: command.value,
				Negated: command.negated,
			}
			solver = smt.Assert(nextAssertion, solver, relation)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastRound:
			relation := smt.NewFloatingPointRoundToIntegralRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.mode, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointRoundToIntegralRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastMinMax:
			relation := smt.NewFloatingPointMinMaxRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.secondSymbolID,
				command.operation, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointMinMaxRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastAdd:
			relation := smt.NewFloatingPointAddRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.secondSymbolID,
				command.mode, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointAddRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastSub:
			relation := smt.NewFloatingPointSubRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.secondSymbolID,
				command.mode, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointSubRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastMul:
			relation := smt.NewFloatingPointMulRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.secondSymbolID,
				command.mode, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointMulRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastDiv:
			relation := smt.NewFloatingPointDivRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.secondSymbolID,
				command.mode, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointDivRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastFMA:
			relation := smt.NewFloatingPointFMARelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.secondSymbolID, command.thirdSymbolID,
				command.mode, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointFMARelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastSqrt:
			relation := smt.NewFloatingPointSqrtRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.mode, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointSqrtRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastRem:
			relation := smt.NewFloatingPointRemRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.secondSymbolID, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointRemRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastConvert:
			relation := smt.NewFloatingPointToBitVectorRelation(
				command.exponentBits, command.significandBits,
				command.width, command.symbolID, command.mode,
				command.signed, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointToBitVectorRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastFromBV:
			relation := smt.NewFloatingPointFromBitVectorRelation(
				command.exponentBits, command.significandBits,
				command.width, command.symbolID, command.mode,
				command.signed, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointFromBitVectorRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastFormat:
			relation := smt.NewFloatingPointFormatConversionRelation(
				command.sourceExponentBits,
				command.sourceSignificandBits,
				command.exponentBits, command.significandBits,
				command.symbolID, command.mode, command.value,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointFormatConversionRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastToReal:
			relation := smt.NewFloatingPointToRealRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.realValue,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointToRealRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastToRealAffine:
			relation := smt.FloatingPointToRealRelation{}
			if command.ordinaryRealTermCount != 0 {
				relation = smt.NewMixedFloatingPointToRealInlineRelation(
					command.realTerms, command.realTermCount,
					command.ordinaryRealTerms, command.ordinaryRealTermCount,
					command.realValue, command.comparison,
				)
			} else {
				relation = smt.NewFloatingPointToRealInlineRelation(
					command.realTerms, command.realTermCount,
					command.realValue, command.comparison,
				)
			}
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointToRealRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastLinearReal:
			constraint := smt.LinearRealConstraint{
				Count:    command.ordinaryRealTermCount,
				Constant: command.realValue,
				Strict:   command.comparison == 2,
			}
			for index := 0; index < command.ordinaryRealTermCount; index++ {
				constraint.Symbols[index] =
					command.ordinaryRealTerms[index].SymbolID
				constraint.Coefficients[index] =
					command.ordinaryRealTerms[index].Coefficient
			}
			if command.negated {
				if command.comparison == 0 {
					return nil, false
				}
				fpFastNegateLinearReal(&constraint)
				constraint.Strict = command.comparison == 1
			}
			solver = smt.Assert(nextAssertion, solver, constraint)
			nextAssertion++
			if command.comparison == 0 {
				fpFastNegateLinearReal(&constraint)
				solver = smt.Assert(nextAssertion, solver, constraint)
				nextAssertion++
			}
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastPredicate:
			relation := smt.NewFloatingPointRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.predicate,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastComparison:
			relation := smt.NewFloatingPointComparisonRelation(
				command.exponentBits, command.significandBits,
				command.symbolID, command.secondSymbolID, command.comparison,
			)
			relation.Negated = command.negated
			solver = smt.AssertFloatingPointComparisonRelation(
				nextAssertion, solver, relation,
			)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastEquality:
			total := command.exponentBits + command.significandBits
			equality := smt.FloatingPointEqualBitVectorTerms(
				command.exponentBits, command.significandBits,
				smt.BitVecConst(total, command.symbolID, command.name),
				smt.BitVecConst(
					total, command.secondSymbolID, command.secondName,
				),
			)
			if command.negated {
				equality = smt.Not{Value: equality}
			}
			solver = smt.Assert(nextAssertion, solver, equality)
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastGroundEquality:
			holds := command.groundHolds
			if command.negated {
				holds = !holds
			}
			groundUnsat = groundUnsat || !holds
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastCheck:
			if groundUnsat {
				result := smt.Check(smt.Assert(
					1, smt.New(), smt.Bool{Value: false},
				)).(smt.Unsatisfiable)
				responses = append(responses, Unsatisfiable{Proof: result.Value})
				continue
			}
			switch result := smt.Check(solver).(type) {
			case smt.Satisfiable:
				responses = append(responses, Satisfiable{Model: result.Value})
			case smt.Unsatisfiable:
				responses = append(responses, Unsatisfiable{Proof: result.Value})
			case smt.Unknown:
				responses = append(responses, Unknown{
					Proof: result.Context, Reason: result.Reason,
				})
			}
		}
	}
	return Executed{Responses: responses}, true
}

func (scanner *fpFastScanner) formula(
	symbols []fpFastSymbol,
) (fpFastCommand, bool) {
	if !scanner.left() {
		return fpFastCommand{}, false
	}
	operator, ok := scanner.atom()
	if !ok {
		return fpFastCommand{}, false
	}
	if scanner.text(operator) == "not" {
		relation, relationOK := scanner.formula(symbols)
		if !relationOK || !scanner.right() {
			return fpFastCommand{}, false
		}
		relation.negated = !relation.negated
		return relation, true
	}
	if predicate, predicateOK := floatingPointPredicateOperator(
		scanner.text(operator),
	); predicateOK {
		symbol, symbolOK := scanner.atom()
		if !symbolOK || !scanner.right() {
			return fpFastCommand{}, false
		}
		found, foundOK := fpFastFindSymbol(scanner.text(symbol), symbols)
		if !foundOK {
			return fpFastCommand{}, false
		}
		return fpFastCommand{
			kind: fpFastPredicate, symbolID: found.id,
			exponentBits:    found.exponentBits,
			significandBits: found.significandBits,
			predicate:       predicate,
		}, true
	}
	if comparison, reverse, equality, comparisonOK :=
		floatingPointComparisonOperator(scanner.text(operator)); comparisonOK {
		leftToken, leftOK := scanner.atom()
		rightToken, rightOK := scanner.atom()
		if !leftOK || !rightOK || !scanner.right() {
			return fpFastCommand{}, false
		}
		left, leftFound := fpFastFindSymbol(scanner.text(leftToken), symbols)
		right, rightFound := fpFastFindSymbol(scanner.text(rightToken), symbols)
		if !leftFound || !rightFound ||
			left.exponentBits != right.exponentBits ||
			left.significandBits != right.significandBits {
			return fpFastCommand{}, false
		}
		if reverse {
			left, right = right, left
		}
		kind := fpFastComparison
		if equality {
			kind = fpFastEquality
		}
		return fpFastCommand{
			kind:     kind,
			symbolID: left.id, secondSymbolID: right.id,
			name: left.name, secondName: right.name,
			exponentBits:    left.exponentBits,
			significandBits: left.significandBits,
			comparison:      comparison,
		}, true
	}
	affineSnapshot := scanner.at
	affineComparison := uint8(0)
	affineReverse := false
	affineOperator := scanner.text(operator)
	affineSupported := affineOperator == "=" || affineOperator == "<=" ||
		affineOperator == "<" || affineOperator == ">=" || affineOperator == ">"
	if affineOperator == "<=" || affineOperator == ">=" {
		affineComparison = 1
	} else if affineOperator == "<" || affineOperator == ">" {
		affineComparison = 2
	}
	affineReverse = affineOperator == ">=" || affineOperator == ">"
	if affineSupported {
		left, leftOK := scanner.realAffine(symbols)
		right, rightOK := scanner.realAffine(symbols)
		if leftOK && rightOK && scanner.right() {
			if affineReverse {
				left, right = right, left
			}
			result := fpFastRealAffine{}
			if result.accumulate(left, smt.NewRational(1, 1)) &&
				result.accumulate(right, smt.NewRational(-1, 1)) {
				count := 0
				for index := 0; index < result.count; index++ {
					if result.terms[index].Coefficient.Sign() == 0 {
						continue
					}
					result.terms[count] = result.terms[index]
					count++
				}
				if count == 0 && result.realCount != 0 {
					return fpFastCommand{
						kind:                  fpFastLinearReal,
						ordinaryRealTermCount: result.realCount,
						ordinaryRealTerms:     result.realTerms,
						realValue:             result.constant,
						comparison:            affineComparison,
					}, true
				} else if count == 0 {
					comparison := smt.CompareRational(
						result.constant, smt.Rational{},
					)
					holds := comparison == 0
					if affineComparison == 1 {
						holds = comparison <= 0
					} else if affineComparison == 2 {
						holds = comparison < 0
					}
					return fpFastCommand{
						kind: fpFastGroundEquality, groundHolds: holds,
					}, true
				}
				if count != 0 {
					return fpFastCommand{
						kind:          fpFastToRealAffine,
						realTermCount: count, realTerms: result.terms,
						ordinaryRealTermCount: result.realCount,
						ordinaryRealTerms:     result.realTerms,
						realValue:             result.constant,
						comparison:            affineComparison,
					}, true
				}
			}
		}
		scanner.at = affineSnapshot
	}
	if scanner.text(operator) != "=" {
		return fpFastCommand{}, false
	}
	left, leftOK := scanner.operand(symbols)
	right, rightOK := scanner.operand(symbols)
	if !leftOK || !rightOK || !scanner.right() {
		return fpFastCommand{}, false
	}
	derived, literal := left, right
	if derived.kind == fpFastLiteralBits ||
		derived.kind == fpFastRealLiteral {
		derived, literal = right, left
	}
	if derived.kind == fpFastExactFloatingBits &&
		literal.kind == fpFastLiteralBits &&
		derived.value.Width() == literal.value.Width() {
		holds := smt.EqualBitVectorValue(derived.value, literal.value)
		return fpFastCommand{
			kind: fpFastGroundEquality, groundHolds: holds,
		}, true
	}
	expectedWidth := derived.exponentBits + derived.significandBits
	if derived.kind == fpFastConversionBits ||
		derived.kind == fpFastBitVectorSymbolBits {
		expectedWidth = derived.width
	}
	if derived.kind == fpFastToRealValue {
		if literal.kind != fpFastRealLiteral {
			return fpFastCommand{}, false
		}
		return fpFastCommand{
			kind:            fpFastToReal,
			symbolID:        derived.symbolID,
			exponentBits:    derived.exponentBits,
			significandBits: derived.significandBits,
			realValue:       literal.realValue,
		}, true
	}
	if literal.kind != fpFastLiteralBits ||
		expectedWidth != literal.value.Width() {
		return fpFastCommand{}, false
	}
	command := fpFastCommand{
		symbolID: derived.symbolID, secondSymbolID: derived.secondSymbolID,
		thirdSymbolID:   derived.thirdSymbolID,
		exponentBits:    derived.exponentBits,
		significandBits: derived.significandBits,
		value:           literal.value, mode: derived.mode,
		operation: derived.operation,
		width:     derived.width, signed: derived.signed,
		sourceExponentBits:    derived.sourceExponentBits,
		sourceSignificandBits: derived.sourceSignificandBits,
	}
	switch derived.kind {
	case fpFastSymbolBits:
		command.kind = fpFastAssign
	case fpFastRoundedBits:
		command.kind = fpFastRound
	case fpFastMinMaxBits:
		command.kind = fpFastMinMax
	case fpFastAddBits:
		command.kind = fpFastAdd
	case fpFastSubBits:
		command.kind = fpFastSub
	case fpFastMulBits:
		command.kind = fpFastMul
	case fpFastDivBits:
		command.kind = fpFastDiv
	case fpFastFMABits:
		command.kind = fpFastFMA
	case fpFastSqrtBits:
		command.kind = fpFastSqrt
	case fpFastRemBits:
		command.kind = fpFastRem
	case fpFastConversionBits:
		command.kind = fpFastConvert
	case fpFastBitVectorSymbolBits:
		command.kind = fpFastAssign
	case fpFastFromBVBits:
		command.kind = fpFastFromBV
	case fpFastFormatBits:
		command.kind = fpFastFormat
	default:
		return fpFastCommand{}, false
	}
	return command, true
}

func (scanner *fpFastScanner) operand(
	symbols []fpFastSymbol,
) (fpFastOperand, bool) {
	snapshot := scanner.at
	if token, ok := scanner.next(); ok && token.kind == fpFastAtom {
		if value, ok := scanner.bitVectorLiteral(token); ok {
			return fpFastOperand{
				kind:  fpFastLiteralBits,
				value: value,
			}, true
		}
		if value, err := smt.ParseRational(scanner.text(token)); err == nil {
			return fpFastOperand{
				kind: fpFastRealLiteral, realValue: value,
			}, true
		}
		if symbol, found := fpFastFindSymbol(scanner.text(token), symbols); found && symbol.bitWidth > 0 {
			return fpFastOperand{
				kind:     fpFastBitVectorSymbolBits,
				symbolID: symbol.id, width: symbol.bitWidth,
			}, true
		}
	}
	scanner.at = snapshot
	if !scanner.left() {
		return fpFastOperand{}, false
	}
	indexedSnapshot := scanner.at
	if scanner.left() {
		marker, markerOK := scanner.atom()
		name, nameOK := scanner.atom()
		width, widthOK := scanner.positiveInt()
		if markerOK && nameOK && widthOK && scanner.text(marker) == "_" &&
			(scanner.text(name) == "fp.to_ubv" ||
				scanner.text(name) == "fp.to_sbv") &&
			scanner.right() {
			modeToken, modeOK := scanner.atom()
			symbolToken, symbolOK := scanner.atom()
			mode, modeFound := fpFastRoundingMode(scanner.text(modeToken))
			symbol, symbolFound := fpFastFindSymbol(
				scanner.text(symbolToken), symbols,
			)
			if modeOK && symbolOK && modeFound && symbolFound &&
				scanner.right() {
				return fpFastOperand{
					kind:            fpFastConversionBits,
					symbolID:        symbol.id,
					exponentBits:    symbol.exponentBits,
					significandBits: symbol.significandBits,
					mode:            mode, width: width,
					signed: scanner.text(name) == "fp.to_sbv",
				}, true
			}
		}
	}
	scanner.at = indexedSnapshot
	operator, operatorOK := scanner.atom()
	if operatorOK && scanner.text(operator) == "fp.to_real" {
		symbolToken, symbolOK := scanner.atom()
		symbol, symbolFound := fpFastFindSymbol(
			scanner.text(symbolToken), symbols,
		)
		if !symbolOK || !symbolFound || symbol.bitWidth != 0 ||
			symbol.exponentBits < 2 || symbol.significandBits < 2 ||
			!scanner.right() {
			return fpFastOperand{}, false
		}
		return fpFastOperand{
			kind: fpFastToRealValue, symbolID: symbol.id,
			exponentBits:    symbol.exponentBits,
			significandBits: symbol.significandBits,
		}, true
	}
	if !operatorOK || scanner.text(operator) != "fp.to_ieee_bv" {
		return fpFastOperand{}, false
	}
	symbolSnapshot := scanner.at
	if symbol, ok := scanner.atom(); ok {
		found, foundOK := fpFastFindSymbol(scanner.text(symbol), symbols)
		if !foundOK || !scanner.right() {
			return fpFastOperand{}, false
		}
		return fpFastOperand{
			kind: fpFastSymbolBits, symbolID: found.id,
			exponentBits:    found.exponentBits,
			significandBits: found.significandBits,
		}, true
	}
	scanner.at = symbolSnapshot
	if !scanner.left() {
		return fpFastOperand{}, false
	}
	fromBVSnapshot := scanner.at
	if scanner.left() {
		marker, markerOK := scanner.atom()
		name, nameOK := scanner.atom()
		exponentBits, exponentOK := scanner.positiveInt()
		significandBits, significandOK := scanner.positiveInt()
		if markerOK && nameOK && exponentOK && significandOK &&
			scanner.text(marker) == "_" &&
			(scanner.text(name) == "to_fp" ||
				scanner.text(name) == "to_fp_unsigned") &&
			exponentBits >= 2 && significandBits >= 2 &&
			scanner.right() {
			modeToken, modeOK := scanner.atom()
			symbolToken, symbolOK := scanner.atom()
			mode, modeFound := fpFastRoundingMode(scanner.text(modeToken))
			rational, rationalError := smt.ParseRational(
				scanner.text(symbolToken),
			)
			symbol, symbolFound := fpFastFindSymbol(
				scanner.text(symbolToken), symbols,
			)
			if modeOK && symbolOK && modeFound &&
				scanner.text(name) == "to_fp" && rationalError == nil &&
				scanner.right() && scanner.right() {
				converted := smt.FloatingPointFromRational(
					exponentBits, significandBits, mode, rational,
				)
				return fpFastOperand{
					kind:            fpFastExactFloatingBits,
					exponentBits:    exponentBits,
					significandBits: significandBits,
					value:           smt.FloatingPointBits(converted),
				}, true
			}
			if modeOK && symbolOK && modeFound && symbolFound &&
				symbol.bitWidth > 0 && scanner.right() && scanner.right() {
				return fpFastOperand{
					kind:     fpFastFromBVBits,
					symbolID: symbol.id, width: symbol.bitWidth,
					exponentBits:    exponentBits,
					significandBits: significandBits,
					mode:            mode,
					signed:          scanner.text(name) == "to_fp",
				}, true
			}
			if modeOK && symbolOK && modeFound && symbolFound &&
				scanner.text(name) == "to_fp" &&
				symbol.exponentBits >= 2 && symbol.significandBits >= 2 &&
				symbol.bitWidth == 0 && scanner.right() && scanner.right() {
				return fpFastOperand{
					kind:                  fpFastFormatBits,
					symbolID:              symbol.id,
					exponentBits:          exponentBits,
					significandBits:       significandBits,
					sourceExponentBits:    symbol.exponentBits,
					sourceSignificandBits: symbol.significandBits,
					mode:                  mode,
				}, true
			}
		}
	}
	scanner.at = fromBVSnapshot
	operation, operationOK := scanner.atom()
	if !operationOK {
		return fpFastOperand{}, false
	}
	switch scanner.text(operation) {
	case "fp":
		signToken, signOK := scanner.next()
		exponentToken, exponentOK := scanner.next()
		significandToken, significandOK := scanner.next()
		sign, signLiteral := scanner.bitVectorLiteral(signToken)
		exponent, exponentLiteral := scanner.bitVectorLiteral(exponentToken)
		significand, significandLiteral := scanner.bitVectorLiteral(significandToken)
		if !signOK || !exponentOK || !significandOK ||
			!signLiteral || !exponentLiteral || !significandLiteral ||
			sign.Width() != 1 || exponent.Width() < 2 || significand.Width() < 1 ||
			!scanner.right() || !scanner.right() {
			return fpFastOperand{}, false
		}
		value := smt.FloatingPointFromComponents(
			exponent.Width(), significand.Width()+1,
			sign, exponent, significand,
		)
		return fpFastOperand{
			kind:         fpFastExactFloatingBits,
			exponentBits: exponent.Width(), significandBits: significand.Width() + 1,
			value: smt.FloatingPointBits(value),
		}, true
	case "_":
		name, nameOK := scanner.atom()
		exponentBits, exponentOK := scanner.positiveInt()
		significandBits, significandOK := scanner.positiveInt()
		if !nameOK || !exponentOK || !significandOK ||
			exponentBits < 2 || significandBits < 2 ||
			!scanner.right() || !scanner.right() {
			return fpFastOperand{}, false
		}
		var value smt.FloatingPointValue
		switch scanner.text(name) {
		case "+zero":
			value = smt.FloatingPointPositiveZero(exponentBits, significandBits)
		case "-zero":
			value = smt.FloatingPointNegativeZero(exponentBits, significandBits)
		case "+oo":
			value = smt.FloatingPointPositiveInfinity(exponentBits, significandBits)
		case "-oo":
			value = smt.FloatingPointNegativeInfinity(exponentBits, significandBits)
		default:
			return fpFastOperand{}, false
		}
		return fpFastOperand{
			kind:         fpFastExactFloatingBits,
			exponentBits: exponentBits, significandBits: significandBits,
			value: smt.FloatingPointBits(value),
		}, true
	case "fp.roundToIntegral":
		mode, modeOK := scanner.atom()
		symbol, symbolOK := scanner.atom()
		if !modeOK || !symbolOK {
			return fpFastOperand{}, false
		}
		roundingMode, roundingModeOK := fpFastRoundingMode(scanner.text(mode))
		found, foundOK := fpFastFindSymbol(scanner.text(symbol), symbols)
		if !roundingModeOK || !foundOK ||
			!scanner.right() || !scanner.right() {
			return fpFastOperand{}, false
		}
		return fpFastOperand{
			kind: fpFastRoundedBits, symbolID: found.id,
			exponentBits:    found.exponentBits,
			significandBits: found.significandBits,
			mode:            roundingMode,
		}, true
	case "fp.sqrt":
		mode, modeOK := scanner.atom()
		symbol, symbolOK := scanner.atom()
		if !modeOK || !symbolOK {
			return fpFastOperand{}, false
		}
		roundingMode, roundingModeOK := fpFastRoundingMode(scanner.text(mode))
		found, foundOK := fpFastFindSymbol(scanner.text(symbol), symbols)
		if !roundingModeOK || !foundOK ||
			!scanner.right() || !scanner.right() {
			return fpFastOperand{}, false
		}
		return fpFastOperand{
			kind: fpFastSqrtBits, symbolID: found.id,
			exponentBits:    found.exponentBits,
			significandBits: found.significandBits,
			mode:            roundingMode,
		}, true
	case "fp.min", "fp.max":
		leftToken, leftOK := scanner.atom()
		rightToken, rightOK := scanner.atom()
		if !leftOK || !rightOK {
			return fpFastOperand{}, false
		}
		left, leftFound := fpFastFindSymbol(scanner.text(leftToken), symbols)
		right, rightFound := fpFastFindSymbol(scanner.text(rightToken), symbols)
		if !leftFound || !rightFound ||
			left.exponentBits != right.exponentBits ||
			left.significandBits != right.significandBits ||
			!scanner.right() || !scanner.right() {
			return fpFastOperand{}, false
		}
		selectedOperation := uint8(smt.FloatingPointOperationMin)
		if scanner.text(operation) == "fp.max" {
			selectedOperation = smt.FloatingPointOperationMax
		}
		return fpFastOperand{
			kind:     fpFastMinMaxBits,
			symbolID: left.id, secondSymbolID: right.id,
			exponentBits:    left.exponentBits,
			significandBits: left.significandBits,
			operation:       selectedOperation,
		}, true
	case "fp.add", "fp.sub", "fp.mul", "fp.div":
		modeToken, modeOK := scanner.atom()
		leftToken, leftOK := scanner.atom()
		rightToken, rightOK := scanner.atom()
		if !modeOK || !leftOK || !rightOK {
			return fpFastOperand{}, false
		}
		mode, modeFound := fpFastRoundingMode(scanner.text(modeToken))
		left, leftFound := fpFastFindSymbol(scanner.text(leftToken), symbols)
		right, rightFound := fpFastFindSymbol(scanner.text(rightToken), symbols)
		if !modeFound || !leftFound || !rightFound ||
			left.exponentBits != right.exponentBits ||
			left.significandBits != right.significandBits ||
			!scanner.right() || !scanner.right() {
			return fpFastOperand{}, false
		}
		kind := uint8(fpFastAddBits)
		if scanner.text(operation) == "fp.sub" {
			kind = fpFastSubBits
		} else if scanner.text(operation) == "fp.mul" {
			kind = fpFastMulBits
		} else if scanner.text(operation) == "fp.div" {
			kind = fpFastDivBits
		}
		return fpFastOperand{
			kind:     kind,
			symbolID: left.id, secondSymbolID: right.id,
			exponentBits:    left.exponentBits,
			significandBits: left.significandBits,
			mode:            mode,
		}, true
	case "fp.fma":
		modeToken, modeOK := scanner.atom()
		leftToken, leftOK := scanner.atom()
		rightToken, rightOK := scanner.atom()
		addendToken, addendOK := scanner.atom()
		if !modeOK || !leftOK || !rightOK || !addendOK {
			return fpFastOperand{}, false
		}
		mode, modeFound := fpFastRoundingMode(scanner.text(modeToken))
		left, leftFound := fpFastFindSymbol(scanner.text(leftToken), symbols)
		right, rightFound := fpFastFindSymbol(scanner.text(rightToken), symbols)
		addend, addendFound := fpFastFindSymbol(scanner.text(addendToken), symbols)
		if !modeFound || !leftFound || !rightFound || !addendFound ||
			left.exponentBits != right.exponentBits ||
			left.significandBits != right.significandBits ||
			left.exponentBits != addend.exponentBits ||
			left.significandBits != addend.significandBits ||
			!scanner.right() || !scanner.right() {
			return fpFastOperand{}, false
		}
		return fpFastOperand{
			kind:     fpFastFMABits,
			symbolID: left.id, secondSymbolID: right.id,
			thirdSymbolID:   addend.id,
			exponentBits:    left.exponentBits,
			significandBits: left.significandBits,
			mode:            mode,
		}, true
	case "fp.rem":
		leftToken, leftOK := scanner.atom()
		rightToken, rightOK := scanner.atom()
		if !leftOK || !rightOK {
			return fpFastOperand{}, false
		}
		left, leftFound := fpFastFindSymbol(scanner.text(leftToken), symbols)
		right, rightFound := fpFastFindSymbol(scanner.text(rightToken), symbols)
		if !leftFound || !rightFound ||
			left.exponentBits != right.exponentBits ||
			left.significandBits != right.significandBits ||
			!scanner.right() || !scanner.right() {
			return fpFastOperand{}, false
		}
		return fpFastOperand{
			kind:     fpFastRemBits,
			symbolID: left.id, secondSymbolID: right.id,
			exponentBits:    left.exponentBits,
			significandBits: left.significandBits,
		}, true
	default:
		return fpFastOperand{}, false
	}
}

func (scanner *fpFastScanner) realAffine(
	symbols []fpFastSymbol,
) (fpFastRealAffine, bool) {
	snapshot := scanner.at
	if token, ok := scanner.atom(); ok {
		value, err := smt.ParseRational(scanner.text(token))
		if err == nil {
			return fpFastRealAffine{constant: value}, true
		}
		if symbol, found := fpFastFindSymbol(
			scanner.text(token), symbols,
		); found && symbol.real {
			return fpFastRealAffine{
				realCount: 1,
				realTerms: [4]smt.FloatingPointToRealRealTerm{{
					SymbolID:    symbol.id,
					Coefficient: smt.NewRational(1, 1),
				}},
			}, true
		}
	}
	scanner.at = snapshot
	if !scanner.left() {
		return fpFastRealAffine{}, false
	}
	operator, ok := scanner.atom()
	if !ok {
		return fpFastRealAffine{}, false
	}
	switch scanner.text(operator) {
	case "fp.to_real":
		symbolToken, symbolOK := scanner.atom()
		symbol, symbolFound := fpFastFindSymbol(
			scanner.text(symbolToken), symbols,
		)
		if !symbolOK || !symbolFound || symbol.bitWidth != 0 ||
			!scanner.right() {
			return fpFastRealAffine{}, false
		}
		return fpFastRealAffine{
			count: 1,
			terms: [4]smt.FloatingPointToRealTerm{{
				ExponentBits:    symbol.exponentBits,
				SignificandBits: symbol.significandBits,
				SymbolID:        symbol.id, Coefficient: smt.NewRational(1, 1),
			}},
		}, true
	case "+":
		result := fpFastRealAffine{}
		operandCount := 0
		for {
			endSnapshot := scanner.at
			if scanner.right() {
				return result, operandCount >= 2
			}
			scanner.at = endSnapshot
			operand, operandOK := scanner.realAffine(symbols)
			if !operandOK || !result.accumulate(
				operand, smt.NewRational(1, 1),
			) {
				return fpFastRealAffine{}, false
			}
			operandCount++
		}
	case "-":
		left, leftOK := scanner.realAffine(symbols)
		if !leftOK {
			return fpFastRealAffine{}, false
		}
		endSnapshot := scanner.at
		if scanner.right() {
			result := fpFastRealAffine{}
			if !result.accumulate(left, smt.NewRational(-1, 1)) {
				return fpFastRealAffine{}, false
			}
			return result, true
		}
		scanner.at = endSnapshot
		right, rightOK := scanner.realAffine(symbols)
		if !rightOK || !scanner.right() {
			return fpFastRealAffine{}, false
		}
		result := fpFastRealAffine{}
		return result, result.accumulate(left, smt.NewRational(1, 1)) &&
			result.accumulate(right, smt.NewRational(-1, 1))
	case "*":
		left, leftOK := scanner.realAffine(symbols)
		right, rightOK := scanner.realAffine(symbols)
		if !leftOK || !rightOK || !scanner.right() {
			return fpFastRealAffine{}, false
		}
		if left.count == 0 {
			result := fpFastRealAffine{}
			return result, result.accumulate(right, left.constant)
		}
		if right.count == 0 {
			result := fpFastRealAffine{}
			return result, result.accumulate(left, right.constant)
		}
	case "/":
		left, leftOK := scanner.realAffine(symbols)
		right, rightOK := scanner.realAffine(symbols)
		if !leftOK || !rightOK || left.count != 0 || right.count != 0 ||
			right.constant.Sign() == 0 || !scanner.right() {
			return fpFastRealAffine{}, false
		}
		return fpFastRealAffine{
			constant: smt.DivideRational(left.constant, right.constant),
		}, true
	}
	return fpFastRealAffine{}, false
}

func (scanner *fpFastScanner) bitVectorLiteral(
	token fpFastToken,
) (smt.BitVectorValue, bool) {
	if token.kind != fpFastAtom {
		return smt.BitVectorValue{}, false
	}
	text := scanner.text(token)
	base, digits, width := 0, "", 0
	switch {
	case strings.HasPrefix(text, "#x") && len(text) > 2:
		base, digits, width = 16, text[2:], 4*(len(text)-2)
	case strings.HasPrefix(text, "#b") && len(text) > 2:
		base, digits, width = 2, text[2:], len(text)-2
	default:
		return smt.BitVectorValue{}, false
	}
	if width > 64 {
		return smt.BitVectorValue{}, false
	}
	value, err := strconv.ParseUint(digits, base, 64)
	if err != nil {
		return smt.BitVectorValue{}, false
	}
	return smt.NewBitVectorUint64(width, value), true
}

func fpFastFindSymbol(name string, symbols []fpFastSymbol) (fpFastSymbol, bool) {
	for _, symbol := range symbols {
		if symbol.name == name {
			return symbol, true
		}
	}
	return fpFastSymbol{}, false
}

func fpFastRoundingMode(
	name string,
) (smt.FloatingPointRoundingMode, bool) {
	switch name {
	case "RNE", "roundNearestTiesToEven":
		return smt.RoundNearestTiesToEven(), true
	case "RNA", "roundNearestTiesToAway":
		return smt.RoundNearestTiesToAway(), true
	case "RTP", "roundTowardPositive":
		return smt.RoundTowardPositive(), true
	case "RTN", "roundTowardNegative":
		return smt.RoundTowardNegative(), true
	case "RTZ", "roundTowardZero":
		return smt.RoundTowardZero(), true
	default:
		return nil, false
	}
}

func (scanner *fpFastScanner) next() (fpFastToken, bool) {
	for scanner.at < len(scanner.source) {
		switch scanner.source[scanner.at] {
		case ' ', '\t', '\n', '\r':
			scanner.at++
			continue
		case ';':
			for scanner.at < len(scanner.source) &&
				scanner.source[scanner.at] != '\n' {
				scanner.at++
			}
			continue
		}
		break
	}
	if scanner.at == len(scanner.source) {
		return fpFastToken{}, false
	}
	start := scanner.at
	switch scanner.source[scanner.at] {
	case '(':
		scanner.at++
		return fpFastToken{kind: fpFastLeft, start: start, end: scanner.at}, true
	case ')':
		scanner.at++
		return fpFastToken{kind: fpFastRight, start: start, end: scanner.at}, true
	}
	for scanner.at < len(scanner.source) {
		switch scanner.source[scanner.at] {
		case ' ', '\t', '\n', '\r', '(', ')', ';':
			return fpFastToken{kind: fpFastAtom, start: start, end: scanner.at}, true
		default:
			scanner.at++
		}
	}
	return fpFastToken{kind: fpFastAtom, start: start, end: scanner.at}, true
}

func (scanner *fpFastScanner) atom() (fpFastToken, bool) {
	token, ok := scanner.next()
	return token, ok && token.kind == fpFastAtom
}

func (scanner *fpFastScanner) left() bool {
	token, ok := scanner.next()
	return ok && token.kind == fpFastLeft
}

func (scanner *fpFastScanner) right() bool {
	token, ok := scanner.next()
	return ok && token.kind == fpFastRight
}

func (scanner *fpFastScanner) positiveInt() (int, bool) {
	token, ok := scanner.atom()
	if !ok {
		return 0, false
	}
	value, err := strconv.Atoi(scanner.text(token))
	return value, err == nil && value > 0
}

func (scanner *fpFastScanner) text(token fpFastToken) string {
	return scanner.source[token.start:token.end]
}
