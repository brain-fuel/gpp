package smtlib

import (
	"fmt"
	"strconv"
	"strings"

	smt "goforge.dev/goplus/std/smt"
)

const (
	sortNumber      = -2
	sortBitVector   = -3
	sortArrayIntInt = -4
	sortArrayBitVec = -5
	sortReal        = -1
	sortBool        = 0
	sortInt         = 1
)

type dynamicTerm struct {
	sort              int
	boolean           smt.Term[smt.BoolSort]
	integer           smt.Term[smt.IntSort]
	real              smt.Term[smt.RealSort]
	bitVector         smt.Term[smt.BitVecSort]
	bitWidth          int
	uninterpreted     smt.Term[smt.UninterpretedSort]
	arrayIntInt       smt.Term[smt.ArraySort[smt.IntSort, smt.IntSort]]
	arrayBitVec       smt.Term[smt.ArraySort[smt.BitVecSort, smt.BitVecSort]]
	arrayIndexWidth   int
	arrayElementWidth int
}

type dynamicUnaryFunction struct {
	domain         int
	rangeSort      int
	value          smt.UnaryFunction
	real           bool
	realValue      smt.SortedUnaryFunction[smt.RealSort, smt.RealSort]
	bitVector      bool
	domainWidth    int
	rangeWidth     int
	bitVectorValue smt.SortedUnaryFunction[smt.BitVecSort, smt.BitVecSort]
}

type dynamicBinaryFunction struct {
	first          int
	second         int
	rangeSort      int
	value          smt.BinaryFunction
	real           bool
	realValue      smt.SortedBinaryFunction[smt.RealSort, smt.RealSort, smt.RealSort]
	bitVector      bool
	firstWidth     int
	secondWidth    int
	rangeWidth     int
	bitVectorValue smt.SortedBinaryFunction[smt.BitVecSort, smt.BitVecSort, smt.BitVecSort]
}

type executor struct {
	solver          smt.Solver
	checkpoints     []smt.Checkpoint
	booleans        map[string]smt.Term[smt.BoolSort]
	integers        map[string]smt.Term[smt.IntSort]
	reals           map[string]smt.Term[smt.RealSort]
	bitVectors      map[string]dynamicTerm
	arrays          map[string]dynamicTerm
	uninterpreted   map[string]dynamicTerm
	sorts           map[string]int
	functions       map[string]dynamicUnaryFunction
	binaryFunctions map[string]dynamicBinaryFunction
	nextSymbol      int
	nextAssertion   int
	lastModel       *smt.Model
	responses       []Response
	errors          []ExecutionError
}

func executeCommands(commands []Command) ([]Response, []ExecutionError) {
	executor := executor{
		solver:          smt.New(),
		booleans:        make(map[string]smt.Term[smt.BoolSort]),
		integers:        make(map[string]smt.Term[smt.IntSort]),
		reals:           make(map[string]smt.Term[smt.RealSort]),
		bitVectors:      make(map[string]dynamicTerm),
		arrays:          make(map[string]dynamicTerm),
		uninterpreted:   make(map[string]dynamicTerm),
		sorts:           make(map[string]int),
		functions:       make(map[string]dynamicUnaryFunction),
		binaryFunctions: make(map[string]dynamicBinaryFunction),
		nextAssertion:   1,
	}
	for index, command := range commands {
		if _, stop := command.(Exit); stop {
			executor.acknowledge(index)
			break
		}
		executor.command(index, command)
	}
	return executor.responses, executor.errors
}

func (executor *executor) command(index int, command Command) {
	switch value := command.(type) {
	case SetLogic, SetOption:
		executor.acknowledge(index)
	case DeclareSort:
		if value.Arity != 0 {
			executor.fail(index, value.At, "only arity-zero uninterpreted sorts are supported")
			return
		}
		if value.Name == "Bool" || value.Name == "Int" {
			executor.fail(index, value.At, "cannot redeclare built-in sort "+value.Name)
			return
		}
		if _, exists := executor.sorts[value.Name]; exists {
			executor.fail(index, value.At, "duplicate sort declaration "+value.Name)
			return
		}
		executor.nextSymbol++
		executor.sorts[value.Name] = executor.nextSymbol
		executor.acknowledge(index)
	case DeclareConst:
		executor.declare(index, value.Name, value.Sort, value.At)
	case DeclareFun:
		if len(value.Domain) == 1 {
			executor.declareUnary(index, value)
			return
		}
		if len(value.Domain) == 2 {
			executor.declareBinary(index, value)
			return
		}
		if len(value.Domain) != 0 {
			executor.fail(index, value.At, "only nullary, unary, and binary declare-fun are supported")
			return
		}
		executor.declare(index, value.Name, value.Range, value.At)
	case Assert:
		term, err := executor.term(value.Term)
		if err != nil || term.sort != sortBool {
			executor.fail(index, value.At, termError("assert requires a Boolean term", err))
			return
		}
		executor.solver = smt.Assert(executor.nextAssertion, executor.solver, term.boolean)
		executor.nextAssertion++
		executor.lastModel = nil
		executor.acknowledge(index)
	case Push:
		for level := 0; level < value.Levels; level++ {
			pushed := smt.Push(executor.solver)
			executor.checkpoints = append(executor.checkpoints, smt.Previous(pushed))
			executor.solver = smt.Current(pushed)
		}
		executor.lastModel = nil
		executor.acknowledge(index)
	case Pop:
		if value.Levels > len(executor.checkpoints) {
			executor.fail(index, value.At, "pop exceeds current scope depth")
			return
		}
		for level := 0; level < value.Levels; level++ {
			last := len(executor.checkpoints) - 1
			executor.solver = smt.Restore(executor.solver, executor.checkpoints[last])
			executor.checkpoints = executor.checkpoints[:last]
		}
		executor.lastModel = nil
		executor.acknowledge(index)
	case CheckSat:
		executor.recordCheck(smt.Check(executor.solver))
	case CheckSatAssuming:
		assumptions := make([]smt.Term[smt.BoolSort], len(value.Assumptions))
		for assumptionIndex, expression := range value.Assumptions {
			term, err := executor.term(expression)
			if err != nil || term.sort != sortBool {
				executor.fail(index, value.At, termError("assumption must be Boolean", err))
				return
			}
			assumptions[assumptionIndex] = term.boolean
		}
		executor.recordAssumptionCheck(smt.CheckAssuming(executor.solver, assumptions...))
	case GetModel:
		if executor.lastModel == nil {
			executor.fail(index, value.At, "get-model requires a preceding satisfiable check")
			return
		}
		executor.responses = append(executor.responses, ModelAvailable{Model: *executor.lastModel})
	case GetValue:
		if executor.lastModel == nil {
			executor.fail(index, value.At, "get-value requires a preceding satisfiable check")
			return
		}
		values := make([]Value, len(value.Terms))
		for valueIndex, expression := range value.Terms {
			term, err := executor.term(expression)
			if err != nil {
				values[valueIndex] = UnavailableValue{Expression: expression, Reason: err.Error()}
				continue
			}
			if term.sort == sortBool {
				result, found := smt.BoolValue(*executor.lastModel, term.boolean)
				if found {
					values[valueIndex] = BooleanValue{Expression: expression, Value: result}
				} else {
					values[valueIndex] = UnavailableValue{Expression: expression, Reason: "model has no Boolean value"}
				}
			} else if term.sort == sortBitVector {
				result, found := smt.BitVecModelValue(*executor.lastModel, term.bitVector)
				if found {
					values[valueIndex] = BitVectorValue{Expression: expression, Value: result}
				} else {
					values[valueIndex] = UnavailableValue{Expression: expression, Reason: "model has no bit-vector value"}
				}
			} else if term.sort == sortReal || term.sort == sortNumber && term.real != nil && term.integer == nil {
				result, found := smt.RealValue(*executor.lastModel, term.real)
				if found {
					values[valueIndex] = RationalValue{Expression: expression, Value: result}
				} else {
					values[valueIndex] = UnavailableValue{Expression: expression, Reason: "model has no rational value"}
				}
			} else {
				result, found := smt.IntegerModelValue(*executor.lastModel, term.integer)
				if found {
					if small, fits := result.Int64(); fits {
						values[valueIndex] = IntegerValue{Expression: expression, Value: small}
					} else {
						values[valueIndex] = ArbitraryIntegerValue{Expression: expression, Value: result}
					}
				} else {
					values[valueIndex] = UnavailableValue{Expression: expression, Reason: "model has no integer value"}
				}
			}
		}
		executor.responses = append(executor.responses, ValuesAvailable{Values: values})
	case RawCommand:
		executor.fail(index, value.At, "unsupported command "+value.Name)
	default:
		executor.fail(index, commandSpan(command), "unsupported command")
	}
}

func (executor *executor) declare(index int, name string, sortExpression SExpr, at Span) {
	if _, exists := executor.booleans[name]; exists {
		executor.fail(index, at, "duplicate declaration "+name)
		return
	}
	if _, exists := executor.integers[name]; exists {
		executor.fail(index, at, "duplicate declaration "+name)
		return
	}
	if _, exists := executor.uninterpreted[name]; exists {
		executor.fail(index, at, "duplicate declaration "+name)
		return
	}
	if _, exists := executor.reals[name]; exists {
		executor.fail(index, at, "duplicate declaration "+name)
		return
	}
	if _, exists := executor.bitVectors[name]; exists {
		executor.fail(index, at, "duplicate declaration "+name)
		return
	}
	if _, exists := executor.arrays[name]; exists {
		executor.fail(index, at, "duplicate declaration "+name)
		return
	}
	if intIntArraySort(sortExpression) {
		executor.nextSymbol++
		executor.arrays[name] = dynamicTerm{sort: sortArrayIntInt, arrayIntInt: smt.ArrayConst[smt.IntSort, smt.IntSort](executor.nextSymbol, name)}
		executor.acknowledge(index)
		return
	}
	if indexWidth, elementWidth, ok := bitVectorArraySortWidths(sortExpression); ok {
		executor.nextSymbol++
		executor.arrays[name] = dynamicTerm{
			sort: sortArrayBitVec, arrayIndexWidth: indexWidth, arrayElementWidth: elementWidth,
			arrayBitVec: smt.BitVectorArrayConst(indexWidth, elementWidth, executor.nextSymbol, name),
		}
		executor.acknowledge(index)
		return
	}
	if width, bitVector := bitVectorSortWidth(sortExpression); bitVector {
		executor.nextSymbol++
		executor.bitVectors[name] = dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecConst(width, executor.nextSymbol, name)}
		executor.acknowledge(index)
		return
	}
	sortName, ok := atomText(sortExpression)
	if !ok {
		executor.fail(index, at, "declaration sort must be Bool or Int")
		return
	}
	executor.nextSymbol++
	switch sortName {
	case "Bool":
		executor.booleans[name] = smt.BoolSymbol{ID: executor.nextSymbol, Name: name}
	case "Int":
		executor.integers[name] = smt.IntSymbol{ID: executor.nextSymbol, Name: name}
	case "Real":
		executor.reals[name] = smt.RealSymbol{ID: executor.nextSymbol, Name: name}
	default:
		sortID, exists := executor.sorts[sortName]
		if !exists {
			executor.fail(index, at, "unsupported sort "+sortName)
			return
		}
		executor.uninterpreted[name] = dynamicTerm{sort: sortID + 2, uninterpreted: smt.UninterpretedConstant(sortID, executor.nextSymbol, name)}
	}
	executor.acknowledge(index)
}

func (executor *executor) declareUnary(index int, declaration DeclareFun) {
	if _, exists := executor.functions[declaration.Name]; exists {
		executor.fail(index, declaration.At, "duplicate function declaration "+declaration.Name)
		return
	}
	if _, exists := executor.binaryFunctions[declaration.Name]; exists {
		executor.fail(index, declaration.At, "duplicate function declaration "+declaration.Name)
		return
	}
	domainName, domainOK := atomText(declaration.Domain[0])
	rangeName, rangeOK := atomText(declaration.Range)
	if domainOK && rangeOK && domainName == "Real" && rangeName == "Real" {
		executor.nextSymbol++
		executor.functions[declaration.Name] = dynamicUnaryFunction{
			real: true, realValue: smt.DeclareRealUnaryFunction(executor.nextSymbol, declaration.Name),
		}
		executor.acknowledge(index)
		return
	}
	if domainWidth, domainBitVector := bitVectorSortWidth(declaration.Domain[0]); domainBitVector {
		if rangeWidth, rangeBitVector := bitVectorSortWidth(declaration.Range); rangeBitVector {
			executor.nextSymbol++
			executor.functions[declaration.Name] = dynamicUnaryFunction{bitVector: true, domainWidth: domainWidth, rangeWidth: rangeWidth, bitVectorValue: smt.DeclareBitVecUnaryFunction(domainWidth, rangeWidth, executor.nextSymbol, declaration.Name)}
			executor.acknowledge(index)
			return
		}
	}
	domain, domainExists := executor.sorts[domainName]
	rangeSort, rangeExists := executor.sorts[rangeName]
	if !domainOK || !rangeOK || !domainExists || !rangeExists {
		executor.fail(index, declaration.At, "unary functions currently require declared uninterpreted domain and range sorts")
		return
	}
	executor.nextSymbol++
	executor.functions[declaration.Name] = dynamicUnaryFunction{domain: domain, rangeSort: rangeSort, value: smt.DeclareUnaryFunction(domain, rangeSort, executor.nextSymbol, declaration.Name)}
	executor.acknowledge(index)
}

func (executor *executor) declareBinary(index int, declaration DeclareFun) {
	if _, exists := executor.functions[declaration.Name]; exists {
		executor.fail(index, declaration.At, "duplicate function declaration "+declaration.Name)
		return
	}
	if _, exists := executor.binaryFunctions[declaration.Name]; exists {
		executor.fail(index, declaration.At, "duplicate function declaration "+declaration.Name)
		return
	}
	firstName, firstOK := atomText(declaration.Domain[0])
	secondName, secondOK := atomText(declaration.Domain[1])
	rangeName, rangeOK := atomText(declaration.Range)
	if firstOK && secondOK && rangeOK && firstName == "Real" && secondName == "Real" && rangeName == "Real" {
		executor.nextSymbol++
		executor.binaryFunctions[declaration.Name] = dynamicBinaryFunction{
			real: true, realValue: smt.DeclareRealBinaryFunction(executor.nextSymbol, declaration.Name),
		}
		executor.acknowledge(index)
		return
	}
	firstWidth, firstBitVector := bitVectorSortWidth(declaration.Domain[0])
	secondWidth, secondBitVector := bitVectorSortWidth(declaration.Domain[1])
	rangeWidth, rangeBitVector := bitVectorSortWidth(declaration.Range)
	if firstBitVector && secondBitVector && rangeBitVector {
		executor.nextSymbol++
		executor.binaryFunctions[declaration.Name] = dynamicBinaryFunction{bitVector: true, firstWidth: firstWidth, secondWidth: secondWidth, rangeWidth: rangeWidth, bitVectorValue: smt.DeclareBitVecBinaryFunction(firstWidth, secondWidth, rangeWidth, executor.nextSymbol, declaration.Name)}
		executor.acknowledge(index)
		return
	}
	first, firstExists := executor.sorts[firstName]
	second, secondExists := executor.sorts[secondName]
	rangeSort, rangeExists := executor.sorts[rangeName]
	if !firstOK || !secondOK || !rangeOK || !firstExists || !secondExists || !rangeExists {
		executor.fail(index, declaration.At, "binary functions currently require declared uninterpreted argument and range sorts")
		return
	}
	executor.nextSymbol++
	executor.binaryFunctions[declaration.Name] = dynamicBinaryFunction{
		first: first, second: second, rangeSort: rangeSort,
		value: smt.DeclareBinaryFunction(first, second, rangeSort, executor.nextSymbol, declaration.Name),
	}
	executor.acknowledge(index)
}

func (executor *executor) term(expression SExpr) (dynamicTerm, error) {
	if atom, ok := expression.(Atom); ok {
		switch atom.Text {
		case "true":
			return dynamicTerm{sort: sortBool, boolean: smt.Bool{Value: true}}, nil
		case "false":
			return dynamicTerm{sort: sortBool, boolean: smt.Bool{Value: false}}, nil
		}
		if value, found := executor.booleans[atom.Text]; found {
			return dynamicTerm{sort: sortBool, boolean: value}, nil
		}
		if value, found := executor.integers[atom.Text]; found {
			return dynamicTerm{sort: sortInt, integer: value}, nil
		}
		if value, found := executor.uninterpreted[atom.Text]; found {
			return value, nil
		}
		if value, found := executor.reals[atom.Text]; found {
			return dynamicTerm{sort: sortReal, real: value}, nil
		}
		if value, found := executor.bitVectors[atom.Text]; found {
			return value, nil
		}
		if value, found := executor.arrays[atom.Text]; found {
			return value, nil
		}
		if strings.HasPrefix(atom.Text, "#x") || strings.HasPrefix(atom.Text, "#b") {
			baseWidth := 4
			prefix := "0x"
			if strings.HasPrefix(atom.Text, "#b") {
				baseWidth, prefix = 1, "0b"
			}
			width := baseWidth * (len(atom.Text) - 2)
			value, err := smt.ParseBitVector(width, prefix+atom.Text[2:])
			if err != nil {
				return dynamicTerm{}, err
			}
			return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVectorTerm(value)}, nil
		}
		if _, numeral := atom.Kind.(NumeralAtom); numeral {
			value, err := strconv.ParseInt(atom.Text, 10, 64)
			exact, exactErr := smt.ParseIntegerValue(atom.Text)
			rational, rationalErr := smt.ParseRational(atom.Text)
			if exactErr != nil {
				return dynamicTerm{}, exactErr
			}
			if rationalErr != nil {
				return dynamicTerm{}, rationalErr
			}
			term := dynamicTerm{sort: sortNumber, real: smt.Real{Value: rational}, integer: smt.IntegerTerm(exact)}
			if err == nil {
				term.integer = smt.Integer{Value: value}
			}
			return term, nil
		}
		if _, decimal := atom.Kind.(DecimalAtom); decimal {
			value, err := smt.ParseRational(atom.Text)
			if err != nil {
				return dynamicTerm{}, err
			}
			return dynamicTerm{sort: sortNumber, real: smt.Real{Value: value}}, nil
		}
		return dynamicTerm{}, fmt.Errorf("unknown symbol %s", atom.Text)
	}
	list, ok := expression.(List)
	if !ok || len(list.Values) == 0 {
		return dynamicTerm{}, fmt.Errorf("term must be a nonempty application")
	}
	operator, ok := atomText(list.Values[0])
	var indexedParameters []int
	constantIntArray := false
	constantBitVecArray := false
	constantArrayIndexWidth, constantArrayElementWidth := 0, 0
	if !ok {
		if intIntConstArrayOperator(list.Values[0]) {
			operator, ok, constantIntArray = "const-array", true, true
		} else if iw, ew, arrayOK := bitVectorConstArrayOperator(list.Values[0]); arrayOK {
			operator, ok, constantBitVecArray = "const-array", true, true
			constantArrayIndexWidth, constantArrayElementWidth = iw, ew
		} else {
			operator, indexedParameters, ok = indexedBitVectorOperator(list.Values[0])
			if !ok {
				return dynamicTerm{}, fmt.Errorf("term operator must be a symbol, const-array qualifier, or supported indexed bit-vector operator")
			}
		}
	}
	arguments := list.Values[1:]
	terms := make([]dynamicTerm, len(arguments))
	for index, argument := range arguments {
		term, err := executor.term(argument)
		if err != nil {
			return dynamicTerm{}, err
		}
		terms[index] = term
	}
	if indexedParameters != nil {
		return buildIndexedBitVectorApplication(operator, indexedParameters, terms)
	}
	if constantIntArray {
		if len(terms) == 1 && (terms[0].sort == sortInt || terms[0].sort == sortNumber && terms[0].integer != nil) {
			return dynamicTerm{sort: sortArrayIntInt, arrayIntInt: smt.ConstArray[smt.IntSort, smt.IntSort](terms[0].integer)}, nil
		}
		return dynamicTerm{}, fmt.Errorf("ill-sorted constant integer array")
	}
	if constantBitVecArray {
		if len(terms) == 1 && terms[0].sort == sortBitVector && terms[0].bitWidth == constantArrayElementWidth {
			return dynamicTerm{sort: sortArrayBitVec, arrayIndexWidth: constantArrayIndexWidth, arrayElementWidth: constantArrayElementWidth,
				arrayBitVec: smt.ConstArray[smt.BitVecSort, smt.BitVecSort](terms[0].bitVector)}, nil
		}
		return dynamicTerm{}, fmt.Errorf("ill-sorted constant bit-vector array")
	}
	if function, found := executor.functions[operator]; found {
		if function.bitVector {
			if len(terms) != 1 || terms[0].sort != sortBitVector || terms[0].bitWidth != function.domainWidth {
				return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
			}
			return dynamicTerm{sort: sortBitVector, bitWidth: function.rangeWidth, bitVector: smt.ApplyBitVecUnary(function.bitVectorValue, terms[0].bitVector)}, nil
		}
		if function.real {
			if len(terms) != 1 || terms[0].sort != sortReal {
				return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
			}
			return dynamicTerm{sort: sortReal, real: smt.ApplySortedUnary(function.realValue, terms[0].real)}, nil
		}
		if len(terms) != 1 || terms[0].sort != function.domain+2 {
			return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
		}
		return dynamicTerm{sort: function.rangeSort + 2, uninterpreted: smt.ApplyUnary(function.value, terms[0].uninterpreted)}, nil
	}
	if function, found := executor.binaryFunctions[operator]; found {
		if function.bitVector {
			if len(terms) != 2 || terms[0].sort != sortBitVector || terms[0].bitWidth != function.firstWidth || terms[1].sort != sortBitVector || terms[1].bitWidth != function.secondWidth {
				return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
			}
			return dynamicTerm{sort: sortBitVector, bitWidth: function.rangeWidth, bitVector: smt.ApplyBitVecBinary(function.bitVectorValue, terms[0].bitVector, terms[1].bitVector)}, nil
		}
		if function.real {
			if len(terms) != 2 || terms[0].sort != sortReal || terms[1].sort != sortReal {
				return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
			}
			return dynamicTerm{sort: sortReal, real: smt.ApplySortedBinary(function.realValue, terms[0].real, terms[1].real)}, nil
		}
		if len(terms) != 2 || terms[0].sort != function.first+2 || terms[1].sort != function.second+2 {
			return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
		}
		return dynamicTerm{sort: function.rangeSort + 2, uninterpreted: smt.ApplyBinary(function.value, terms[0].uninterpreted, terms[1].uninterpreted)}, nil
	}
	return buildApplication(operator, terms)
}

func buildApplication(operator string, terms []dynamicTerm) (dynamicTerm, error) {
	if operator == "select" && len(terms) == 2 && terms[0].sort == sortArrayBitVec && terms[1].sort == sortBitVector && terms[1].bitWidth == terms[0].arrayIndexWidth {
		return dynamicTerm{sort: sortBitVector, bitWidth: terms[0].arrayElementWidth, bitVector: smt.Select(terms[0].arrayBitVec, terms[1].bitVector)}, nil
	}
	if operator == "store" && len(terms) == 3 && terms[0].sort == sortArrayBitVec && terms[1].sort == sortBitVector && terms[1].bitWidth == terms[0].arrayIndexWidth && terms[2].sort == sortBitVector && terms[2].bitWidth == terms[0].arrayElementWidth {
		return dynamicTerm{sort: sortArrayBitVec, arrayIndexWidth: terms[0].arrayIndexWidth, arrayElementWidth: terms[0].arrayElementWidth,
			arrayBitVec: smt.Store(terms[0].arrayBitVec, terms[1].bitVector, terms[2].bitVector)}, nil
	}
	if operator == "select" && len(terms) == 2 && terms[0].sort == sortArrayIntInt && (terms[1].sort == sortInt || terms[1].sort == sortNumber && terms[1].integer != nil) {
		return dynamicTerm{sort: sortInt, integer: smt.Select(terms[0].arrayIntInt, terms[1].integer)}, nil
	}
	if operator == "store" && len(terms) == 3 && terms[0].sort == sortArrayIntInt && (terms[1].sort == sortInt || terms[1].sort == sortNumber && terms[1].integer != nil) && (terms[2].sort == sortInt || terms[2].sort == sortNumber && terms[2].integer != nil) {
		return dynamicTerm{sort: sortArrayIntInt, arrayIntInt: smt.Store(terms[0].arrayIntInt, terms[1].integer, terms[2].integer)}, nil
	}
	if operator == "concat" && len(terms) == 2 && terms[0].sort == sortBitVector && terms[1].sort == sortBitVector {
		return dynamicTerm{sort: sortBitVector, bitWidth: terms[0].bitWidth + terms[1].bitWidth, bitVector: smt.BitVecConcat(terms[0].bitWidth, terms[1].bitWidth, terms[0].bitVector, terms[1].bitVector)}, nil
	}
	bitVectors := func() ([]smt.Term[smt.BitVecSort], int, bool) {
		if len(terms) == 0 || terms[0].sort != sortBitVector {
			return nil, 0, false
		}
		width := terms[0].bitWidth
		values := make([]smt.Term[smt.BitVecSort], len(terms))
		for index, term := range terms {
			if term.sort != sortBitVector || term.bitWidth != width {
				return nil, 0, false
			}
			values[index] = term.bitVector
		}
		return values, width, true
	}
	booleans := func() ([]smt.Term[smt.BoolSort], bool) {
		values := make([]smt.Term[smt.BoolSort], len(terms))
		for index, term := range terms {
			if term.sort != sortBool {
				return nil, false
			}
			values[index] = term.boolean
		}
		return values, true
	}
	integers := func() ([]smt.Term[smt.IntSort], bool) {
		values := make([]smt.Term[smt.IntSort], len(terms))
		for index, term := range terms {
			if term.sort != sortInt && (term.sort != sortNumber || term.integer == nil) {
				return nil, false
			}
			values[index] = term.integer
		}
		return values, true
	}
	reals := func() ([]smt.Term[smt.RealSort], bool) {
		values := make([]smt.Term[smt.RealSort], len(terms))
		for index, term := range terms {
			if term.sort != sortReal && term.sort != sortNumber || term.real == nil {
				return nil, false
			}
			values[index] = term.real
		}
		return values, true
	}
	hasReal := func() bool {
		for _, term := range terms {
			if term.sort == sortReal || term.sort == sortNumber && term.integer == nil {
				return true
			}
		}
		return false
	}
	switch operator {
	case "ubv_to_int":
		if len(terms) == 1 && terms[0].sort == sortBitVector {
			return dynamicTerm{sort: sortInt, integer: smt.BitVecToNat(terms[0].bitVector)}, nil
		}
	case "sbv_to_int":
		if len(terms) == 1 && terms[0].sort == sortBitVector {
			return dynamicTerm{sort: sortInt, integer: smt.BitVecToInt(terms[0].bitVector)}, nil
		}
	case "not":
		if values, ok := booleans(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortBool, boolean: smt.Not{Value: values[0]}}, nil
		}
	case "and":
		if values, ok := booleans(); ok {
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: values}}, nil
		}
	case "or":
		if values, ok := booleans(); ok {
			return dynamicTerm{sort: sortBool, boolean: smt.Or{Values: values}}, nil
		}
	case "=>":
		if values, ok := booleans(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortBool, boolean: smt.Implies{Left: values[0], Right: values[1]}}, nil
		}
	case "distinct":
		if values, ok := integers(); ok {
			if len(values) < 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.Bool{Value: true}}, nil
			}
			disequalities := make([]smt.Term[smt.BoolSort], 0, len(values)*(len(values)-1)/2)
			for left := 0; left < len(values); left++ {
				for right := left + 1; right < len(values); right++ {
					disequalities = append(disequalities, smt.Not{Value: smt.Equal{Left: values[left], Right: values[right]}})
				}
			}
			if len(disequalities) == 1 {
				return dynamicTerm{sort: sortBool, boolean: disequalities[0]}, nil
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: disequalities}}, nil
		}
	case "=":
		if len(terms) >= 2 && terms[0].sort == sortArrayBitVec {
			equalities := make([]smt.Term[smt.BoolSort], len(terms)-1)
			for index := 1; index < len(terms); index++ {
				if terms[index].sort != sortArrayBitVec || terms[index].arrayIndexWidth != terms[0].arrayIndexWidth || terms[index].arrayElementWidth != terms[0].arrayElementWidth {
					break
				}
				equalities[index-1] = smt.Equal{Left: terms[index-1].arrayBitVec, Right: terms[index].arrayBitVec}
			}
			if len(equalities) == 1 && equalities[0] != nil {
				return dynamicTerm{sort: sortBool, boolean: equalities[0]}, nil
			}
		}
		if len(terms) >= 2 && terms[0].sort == sortArrayIntInt {
			equalities := make([]smt.Term[smt.BoolSort], len(terms)-1)
			for index := 1; index < len(terms); index++ {
				if terms[index].sort != sortArrayIntInt {
					break
				}
				equalities[index-1] = smt.Equal{Left: terms[index-1].arrayIntInt, Right: terms[index].arrayIntInt}
			}
			if len(equalities) == 1 && equalities[0] != nil {
				return dynamicTerm{sort: sortBool, boolean: equalities[0]}, nil
			}
		}
		if values, _, ok := bitVectors(); ok && len(values) >= 2 {
			equalities := make([]smt.Term[smt.BoolSort], len(values)-1)
			for index := 1; index < len(values); index++ {
				equalities[index-1] = smt.Equal{Left: values[index-1], Right: values[index]}
			}
			if len(equalities) == 1 {
				return dynamicTerm{sort: sortBool, boolean: equalities[0]}, nil
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: equalities}}, nil
		}
		if values, ok := booleans(); ok && len(values) >= 2 {
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.Equal{Left: values[0], Right: values[1]}}, nil
			}
			equalities := make([]smt.Term[smt.BoolSort], len(values)-1)
			for index := 1; index < len(values); index++ {
				equalities[index-1] = smt.Equal{Left: values[index-1], Right: values[index]}
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: equalities}}, nil
		}
		if values, ok := reals(); ok && len(values) >= 2 && hasReal() {
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.Equal{Left: values[0], Right: values[1]}}, nil
			}
			equalities := make([]smt.Term[smt.BoolSort], len(values)-1)
			for index := 1; index < len(values); index++ {
				equalities[index-1] = smt.Equal{Left: values[index-1], Right: values[index]}
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: equalities}}, nil
		}
		if values, ok := integers(); ok && len(values) >= 2 {
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.Equal{Left: values[0], Right: values[1]}}, nil
			}
			equalities := make([]smt.Term[smt.BoolSort], len(values)-1)
			for index := 1; index < len(values); index++ {
				equalities[index-1] = smt.Equal{Left: values[index-1], Right: values[index]}
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: equalities}}, nil
		}
		if len(terms) >= 2 && terms[0].sort >= 2 {
			if len(terms) == 2 {
				if terms[1].sort != terms[0].sort {
					return dynamicTerm{}, fmt.Errorf("unsupported or ill-sorted application %s", operator)
				}
				return dynamicTerm{sort: sortBool, boolean: smt.Equal{Left: terms[0].uninterpreted, Right: terms[1].uninterpreted}}, nil
			}
			equalities := make([]smt.Term[smt.BoolSort], len(terms)-1)
			for index := 1; index < len(terms); index++ {
				if terms[index].sort != terms[0].sort {
					return dynamicTerm{}, fmt.Errorf("unsupported or ill-sorted application %s", operator)
				}
				equalities[index-1] = smt.Equal{Left: terms[index-1].uninterpreted, Right: terms[index].uninterpreted}
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: equalities}}, nil
		}
	case "+":
		if values, ok := reals(); ok && hasReal() {
			return dynamicTerm{sort: sortReal, real: smt.RealAdd{Values: values}}, nil
		}
		if values, ok := integers(); ok {
			return dynamicTerm{sort: sortInt, integer: smt.Add{Values: values}}, nil
		}
	case "-":
		if values, ok := reals(); ok && hasReal() && len(values) == 1 {
			return dynamicTerm{sort: sortReal, real: smt.RealScale{Coefficient: smt.NewRational(-1, 1), Value: values[0]}}, nil
		}
		if values, ok := reals(); ok && hasReal() && len(values) == 2 {
			return dynamicTerm{sort: sortReal, real: smt.RealSubtract{Left: values[0], Right: values[1]}}, nil
		}
		if values, ok := integers(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortInt, integer: smt.Subtract{Left: smt.Integer{Value: 0}, Right: values[0]}}, nil
		}
		if values, ok := integers(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortInt, integer: smt.Subtract{Left: values[0], Right: values[1]}}, nil
		}
	case "<=":
		if values, ok := reals(); ok && len(values) == 2 && hasReal() {
			return dynamicTerm{sort: sortBool, boolean: smt.RealLessEqual{Left: values[0], Right: values[1]}}, nil
		}
		if values, ok := integers(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortBool, boolean: smt.LessEqual{Left: values[0], Right: values[1]}}, nil
		}
	case "<":
		if values, ok := reals(); ok && len(values) == 2 && hasReal() {
			return dynamicTerm{sort: sortBool, boolean: smt.RealLess{Left: values[0], Right: values[1]}}, nil
		}
		if values, ok := integers(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortBool, boolean: smt.Less{Left: values[0], Right: values[1]}}, nil
		}
	case "div":
		if values, ok := integers(); ok && len(values) == 2 {
			if divisor, exact := smt.ExactIntegerConstant(values[1]); exact && smt.CompareIntegerValue(divisor, smt.IntegerValue{}) > 0 {
				return dynamicTerm{sort: sortInt, integer: smt.DivInteger(values[0], divisor)}, nil
			}
		}
	case "mod":
		if values, ok := integers(); ok && len(values) == 2 {
			if divisor, exact := smt.ExactIntegerConstant(values[1]); exact && smt.CompareIntegerValue(divisor, smt.IntegerValue{}) > 0 {
				return dynamicTerm{sort: sortInt, integer: smt.ModInteger(values[0], divisor)}, nil
			}
		}
	case ">=":
		if values, ok := reals(); ok && len(values) == 2 && hasReal() {
			return dynamicTerm{sort: sortBool, boolean: smt.RealLessEqual{Left: values[1], Right: values[0]}}, nil
		}
		if values, ok := integers(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortBool, boolean: smt.LessEqual{Left: values[1], Right: values[0]}}, nil
		}
	case ">":
		if values, ok := reals(); ok && len(values) == 2 && hasReal() {
			return dynamicTerm{sort: sortBool, boolean: smt.RealLess{Left: values[1], Right: values[0]}}, nil
		}
		if values, ok := integers(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortBool, boolean: smt.Less{Left: values[1], Right: values[0]}}, nil
		}
	case "*":
		if len(terms) == 2 {
			if coefficient, ok := integerConstant(terms[0]); ok && terms[1].sort == sortInt {
				return dynamicTerm{sort: sortInt, integer: smt.ScaleInteger(coefficient, terms[1].integer)}, nil
			}
			if coefficient, ok := integerConstant(terms[1]); ok && terms[0].sort == sortInt {
				return dynamicTerm{sort: sortInt, integer: smt.ScaleInteger(coefficient, terms[0].integer)}, nil
			}
			if coefficient, ok := rationalConstant(terms[0]); ok && terms[1].sort == sortReal {
				return dynamicTerm{sort: sortReal, real: smt.RealScale{Coefficient: coefficient, Value: terms[1].real}}, nil
			}
			if coefficient, ok := rationalConstant(terms[1]); ok && terms[0].sort == sortReal {
				return dynamicTerm{sort: sortReal, real: smt.RealScale{Coefficient: coefficient, Value: terms[0].real}}, nil
			}
		}
	case "/":
		if len(terms) == 2 {
			left, leftOK := rationalConstant(terms[0])
			right, rightOK := rationalConstant(terms[1])
			if leftOK && rightOK && right.Sign() != 0 {
				return dynamicTerm{sort: sortReal, real: smt.Real{Value: smt.DivideRational(left, right)}}, nil
			}
			if denominator, ok := rationalConstant(terms[1]); ok && denominator.Sign() != 0 && terms[0].sort == sortReal {
				inverse := smt.DivideRational(smt.NewRational(1, 1), denominator)
				return dynamicTerm{sort: sortReal, real: smt.RealScale{Coefficient: inverse, Value: terms[0].real}}, nil
			}
		}
	case "ite":
		if len(terms) == 3 && terms[0].sort == sortBool && terms[1].sort == terms[2].sort {
			if terms[1].sort == sortBool {
				return dynamicTerm{sort: sortBool, boolean: smt.If[smt.BoolSort]{Condition: terms[0].boolean, Then: terms[1].boolean, Else: terms[2].boolean}}, nil
			}
			if terms[1].sort == sortReal {
				return dynamicTerm{sort: sortReal, real: smt.If[smt.RealSort]{Condition: terms[0].boolean, Then: terms[1].real, Else: terms[2].real}}, nil
			}
			return dynamicTerm{sort: sortInt, integer: smt.If[smt.IntSort]{Condition: terms[0].boolean, Then: terms[1].integer, Else: terms[2].integer}}, nil
		}
	}
	if values, width, ok := bitVectors(); ok {
		switch operator {
		case "bvnot":
			if len(values) == 1 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecNot(values[0])}, nil
			}
		case "bvand":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecAnd(values[0], values[1])}, nil
			}
		case "bvor":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecOr(values[0], values[1])}, nil
			}
		case "bvxor":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecXor(values[0], values[1])}, nil
			}
		case "bvadd":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecAdd(values[0], values[1])}, nil
			}
		case "bvsub":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecSub(values[0], values[1])}, nil
			}
		case "bvmul":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecMul(values[0], values[1])}, nil
			}
		case "bvshl":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecSHL(values[0], values[1])}, nil
			}
		case "bvlshr":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecLSHR(values[0], values[1])}, nil
			}
		case "bvashr":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecASHR(values[0], values[1])}, nil
			}
		case "bvudiv":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecUDiv(values[0], values[1])}, nil
			}
		case "bvurem":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecURem(values[0], values[1])}, nil
			}
		case "bvsdiv":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecSDiv(values[0], values[1])}, nil
			}
		case "bvsrem":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBitVector, bitWidth: width, bitVector: smt.BitVecSRem(values[0], values[1])}, nil
			}
		case "bvult":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecULT(values[0], values[1])}, nil
			}
		case "bvule":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecULE(values[0], values[1])}, nil
			}
		case "bvslt":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecSLT(values[0], values[1])}, nil
			}
		case "bvsle":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecSLE(values[0], values[1])}, nil
			}
		case "bvuaddo":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecUAddOverflow(values[0], values[1])}, nil
			}
		case "bvsaddo":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecSAddOverflow(values[0], values[1])}, nil
			}
		case "bvusubo":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecUSubOverflow(values[0], values[1])}, nil
			}
		case "bvssubo":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecSSubOverflow(values[0], values[1])}, nil
			}
		case "bvumulo":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecUMulOverflow(values[0], values[1])}, nil
			}
		case "bvsmulo":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecSMulOverflow(values[0], values[1])}, nil
			}
		case "bvsdivo":
			if len(values) == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecSDivOverflow(values[0], values[1])}, nil
			}
		case "bvnego":
			if len(values) == 1 {
				return dynamicTerm{sort: sortBool, boolean: smt.BitVecNegOverflow(values[0])}, nil
			}
		}
	}
	return dynamicTerm{}, fmt.Errorf("unsupported or ill-sorted application %s", operator)
}

func indexedBitVectorOperator(expression SExpr) (string, []int, bool) {
	list, ok := expression.(List)
	if !ok || len(list.Values) < 3 {
		return "", nil, false
	}
	marker, markerOK := atomText(list.Values[0])
	name, nameOK := atomText(list.Values[1])
	if !markerOK || !nameOK || marker != "_" {
		return "", nil, false
	}
	parameters := make([]int, len(list.Values)-2)
	for index, expression := range list.Values[2:] {
		text, ok := atomText(expression)
		if !ok {
			return "", nil, false
		}
		value, err := strconv.Atoi(text)
		if err != nil || value < 0 {
			return "", nil, false
		}
		parameters[index] = value
	}
	return name, parameters, true
}

func buildIndexedBitVectorApplication(operator string, parameters []int, terms []dynamicTerm) (dynamicTerm, error) {
	if operator == "int_to_bv" {
		if len(parameters) == 1 && parameters[0] > 0 && len(terms) == 1 && (terms[0].sort == sortInt || terms[0].sort == sortNumber && terms[0].integer != nil) {
			return dynamicTerm{sort: sortBitVector, bitWidth: parameters[0], bitVector: smt.IntToBitVec(parameters[0], terms[0].integer)}, nil
		}
		return dynamicTerm{}, fmt.Errorf("ill-sorted indexed application %s", operator)
	}
	if len(terms) != 1 || terms[0].sort != sortBitVector {
		return dynamicTerm{}, fmt.Errorf("ill-sorted indexed application %s", operator)
	}
	value := terms[0]
	switch operator {
	case "extract":
		if len(parameters) == 2 && parameters[1] <= parameters[0] && parameters[0] < value.bitWidth {
			return dynamicTerm{sort: sortBitVector, bitWidth: parameters[0] - parameters[1] + 1, bitVector: smt.BitVecExtract(parameters[0], parameters[1], value.bitVector)}, nil
		}
	case "zero_extend":
		if len(parameters) == 1 {
			return dynamicTerm{sort: sortBitVector, bitWidth: value.bitWidth + parameters[0], bitVector: smt.BitVecZeroExtend(parameters[0], value.bitVector)}, nil
		}
	case "sign_extend":
		if len(parameters) == 1 {
			return dynamicTerm{sort: sortBitVector, bitWidth: value.bitWidth + parameters[0], bitVector: smt.BitVecSignExtend(parameters[0], value.bitVector)}, nil
		}
	case "rotate_left":
		if len(parameters) == 1 {
			return dynamicTerm{sort: sortBitVector, bitWidth: value.bitWidth, bitVector: smt.BitVecRotateLeft(parameters[0], value.bitVector)}, nil
		}
	case "rotate_right":
		if len(parameters) == 1 {
			return dynamicTerm{sort: sortBitVector, bitWidth: value.bitWidth, bitVector: smt.BitVecRotateRight(parameters[0], value.bitVector)}, nil
		}
	case "repeat":
		if len(parameters) == 1 && parameters[0] > 0 {
			return dynamicTerm{sort: sortBitVector, bitWidth: value.bitWidth * parameters[0], bitVector: smt.BitVecRepeat(parameters[0], value.bitVector)}, nil
		}
	}
	return dynamicTerm{}, fmt.Errorf("unsupported indexed bit-vector application %s", operator)
}

func bitVectorSortWidth(expression SExpr) (int, bool) {
	list, ok := expression.(List)
	if !ok || len(list.Values) != 3 {
		return 0, false
	}
	marker, markerOK := atomText(list.Values[0])
	name, nameOK := atomText(list.Values[1])
	widthText, widthOK := atomText(list.Values[2])
	if !markerOK || !nameOK || !widthOK || marker != "_" || name != "BitVec" {
		return 0, false
	}
	width, err := strconv.Atoi(widthText)
	return width, err == nil && width > 0
}

func intIntArraySort(expression SExpr) bool {
	list, ok := expression.(List)
	if !ok || len(list.Values) != 3 {
		return false
	}
	name, nameOK := atomText(list.Values[0])
	index, indexOK := atomText(list.Values[1])
	element, elementOK := atomText(list.Values[2])
	return nameOK && indexOK && elementOK && name == "Array" && index == "Int" && element == "Int"
}

func bitVectorArraySortWidths(expression SExpr) (int, int, bool) {
	list, ok := expression.(List)
	if !ok || len(list.Values) != 3 {
		return 0, 0, false
	}
	name, nameOK := atomText(list.Values[0])
	indexWidth, indexOK := bitVectorSortWidth(list.Values[1])
	elementWidth, elementOK := bitVectorSortWidth(list.Values[2])
	return indexWidth, elementWidth, nameOK && name == "Array" && indexOK && elementOK
}

func intIntConstArrayOperator(expression SExpr) bool {
	list, ok := expression.(List)
	if !ok || len(list.Values) != 3 {
		return false
	}
	as, asOK := atomText(list.Values[0])
	constant, constantOK := atomText(list.Values[1])
	return asOK && constantOK && as == "as" && constant == "const" && intIntArraySort(list.Values[2])
}

func bitVectorConstArrayOperator(expression SExpr) (int, int, bool) {
	list, ok := expression.(List)
	if !ok || len(list.Values) != 3 {
		return 0, 0, false
	}
	as, asOK := atomText(list.Values[0])
	constant, constantOK := atomText(list.Values[1])
	indexWidth, elementWidth, arrayOK := bitVectorArraySortWidths(list.Values[2])
	return indexWidth, elementWidth, asOK && constantOK && as == "as" && constant == "const" && arrayOK
}

func rationalConstant(term dynamicTerm) (smt.Rational, bool) {
	value, ok := term.real.(smt.Real)
	return value.Value, ok
}

func integerConstant(term dynamicTerm) (smt.IntegerValue, bool) {
	if term.integer == nil {
		return smt.IntegerValue{}, false
	}
	return smt.ExactIntegerConstant(term.integer)
}

func (executor *executor) recordCheck(result smt.CheckResult) {
	switch value := result.(type) {
	case smt.Satisfiable:
		model := value.Value
		executor.lastModel = &model
		executor.responses = append(executor.responses, Satisfiable{Model: model})
	case smt.Unsatisfiable:
		executor.lastModel = nil
		executor.responses = append(executor.responses, Unsatisfiable{Proof: value.Value})
	case smt.Unknown:
		executor.lastModel = nil
		executor.responses = append(executor.responses, Unknown{Proof: value.Context, Reason: value.Reason})
	}
}

func (executor *executor) recordAssumptionCheck(result smt.AssumptionCheckResult) {
	switch value := result.(type) {
	case smt.AssumptionsSatisfiable:
		model := value.Value
		executor.lastModel = &model
		executor.responses = append(executor.responses, Satisfiable{Model: model})
	case smt.AssumptionsUnsatisfiable:
		executor.lastModel = nil
		executor.responses = append(executor.responses, AssumptionsUnsatisfiable{Proof: value.Value, Indices: append([]int(nil), value.Indices...)})
	case smt.AssumptionsUnknown:
		executor.lastModel = nil
		executor.responses = append(executor.responses, Unknown{Proof: value.Context, Reason: value.Reason})
	}
}

func (executor *executor) acknowledge(index int) {
	executor.responses = append(executor.responses, Acknowledged{CommandIndex: index})
}
func (executor *executor) fail(index int, at Span, message string) {
	executor.errors = append(executor.errors, ExecutionError{CommandIndex: index, Message: message, At: at})
}
func atomText(expression SExpr) (string, bool) { atom, ok := expression.(Atom); return atom.Text, ok }
func termError(fallback string, err error) string {
	if err != nil {
		return err.Error()
	}
	return fallback
}

func commandSpan(command Command) Span {
	switch value := command.(type) {
	case SetLogic:
		return value.At
	case SetOption:
		return value.At
	case DeclareSort:
		return value.At
	case DeclareConst:
		return value.At
	case DeclareFun:
		return value.At
	case Assert:
		return value.At
	case CheckSat:
		return value.At
	case CheckSatAssuming:
		return value.At
	case Push:
		return value.At
	case Pop:
		return value.At
	case GetModel:
		return value.At
	case GetValue:
		return value.At
	case Exit:
		return value.At
	case RawCommand:
		return value.At
	default:
		return Span{}
	}
}
