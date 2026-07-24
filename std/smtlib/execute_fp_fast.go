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
	fpFastPredicate
	fpFastComparison
	fpFastEquality
	fpFastGroundEquality
	fpFastCheck
)

type fpFastCommand struct {
	kind                          uint8
	symbolID, secondSymbolID      int
	exponentBits                  int
	significandBits, commandIndex int
	name, secondName              string
	value                         smt.BitVectorValue
	mode                          smt.FloatingPointRoundingMode
	predicate                     uint8
	comparison                    uint8
	operation                     uint8
	negated                       bool
	groundHolds                   bool
}

type fpFastSymbol struct {
	name             string
	id, exponentBits int
	significandBits  int
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
	value                  smt.BitVectorValue
	mode                   smt.FloatingPointRoundingMode
	secondSymbolID         int
	operation              uint8
}

const (
	fpFastSymbolBits uint8 = iota + 1
	fpFastRoundedBits
	fpFastMinMaxBits
	fpFastAddBits
	fpFastSubBits
	fpFastMulBits
	fpFastDivBits
	fpFastExactFloatingBits
	fpFastLiteralBits
)

func executeFloatingPointFast(source string) (ExecutionResult, bool) {
	if !strings.Contains(source, "QF_FP") {
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
			if !logicOK || scanner.text(logic) != "QF_FP" ||
				!scanner.right() {
				return nil, false
			}
			command.kind = fpFastAcknowledge
		case "declare-const":
			name, nameOK := scanner.atom()
			if !nameOK || symbolCount == len(symbols) ||
				!scanner.left() {
				return nil, false
			}
			marker, markerOK := scanner.atom()
			sort, sortOK := scanner.atom()
			exponent, exponentOK := scanner.positiveInt()
			significand, significandOK := scanner.positiveInt()
			if !markerOK || !sortOK || !exponentOK || !significandOK ||
				scanner.text(marker) != "_" ||
				scanner.text(sort) != "FloatingPoint" ||
				exponent < 2 || significand < 2 ||
				!scanner.right() || !scanner.right() {
				return nil, false
			}
			nameText := scanner.text(name)
			for index := 0; index < symbolCount; index++ {
				if symbols[index].name == nameText {
					return nil, false
				}
			}
			symbolCount++
			symbols[symbolCount-1] = fpFastSymbol{
				name: nameText, id: symbolCount,
				exponentBits: exponent, significandBits: significand,
			}
			command.kind = fpFastDeclare
			command.symbolID, command.name = symbolCount, nameText
			command.exponentBits, command.significandBits = exponent, significand
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
	for index := 0; index < commandCount; index++ {
		command := commands[index]
		switch command.kind {
		case fpFastAcknowledge, fpFastDeclare:
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastAssign:
			relation := smt.BitVectorRelation{
				Width:    command.exponentBits + command.significandBits,
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
			solver = smt.Assert(nextAssertion, solver, smt.Bool{Value: holds})
			nextAssertion++
			responses = append(responses, Acknowledged{CommandIndex: command.commandIndex})
		case fpFastCheck:
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
	if scanner.text(operator) != "=" {
		return fpFastCommand{}, false
	}
	left, leftOK := scanner.operand(symbols)
	right, rightOK := scanner.operand(symbols)
	if !leftOK || !rightOK || !scanner.right() {
		return fpFastCommand{}, false
	}
	derived, literal := left, right
	if derived.kind == fpFastLiteralBits {
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
	if literal.kind != fpFastLiteralBits ||
		derived.exponentBits+derived.significandBits != literal.value.Width() {
		return fpFastCommand{}, false
	}
	command := fpFastCommand{
		symbolID: derived.symbolID, secondSymbolID: derived.secondSymbolID,
		exponentBits:    derived.exponentBits,
		significandBits: derived.significandBits,
		value:           literal.value, mode: derived.mode,
		operation: derived.operation,
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
	}
	scanner.at = snapshot
	if !scanner.left() {
		return fpFastOperand{}, false
	}
	operator, operatorOK := scanner.atom()
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
	default:
		return fpFastOperand{}, false
	}
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
