package smtlib

import (
	"fmt"
	"strconv"
	"strings"

	smt "goforge.dev/goplus/std/smt"
)

const (
	sortNumber       = -2
	sortBitVector    = -3
	sortArrayIntInt  = -4
	sortArrayBitVec  = -5
	sortString       = -6
	sortRegexString  = -7
	sortReal         = -1
	sortBool         = 0
	sortInt          = 1
	sortDatatypeSelf = 2
	sortDatatypeBase = -1000000
)

type dynamicTerm struct {
	sort                 int
	boolean              smt.Term[smt.BoolSort]
	integer              smt.Term[smt.IntSort]
	real                 smt.Term[smt.RealSort]
	bitVector            smt.Term[smt.BitVecSort]
	stringValue          smt.Term[smt.StringSort]
	regexString          smt.Regex[smt.StringSort]
	bitWidth             int
	uninterpreted        smt.Term[smt.UninterpretedSort]
	arrayIntInt          smt.Term[smt.ArraySort[smt.IntSort, smt.IntSort]]
	arrayBitVec          smt.Term[smt.ArraySort[smt.BitVecSort, smt.BitVecSort]]
	arrayIndexWidth      int
	arrayElementWidth    int
	datatype             smt.Term[smt.DatatypeSort]
	datatypeID           int
	constructorCount     int
	selectorTarget       smt.Term[smt.DatatypeSort]
	selectorDatatypeID   int
	selectorConstructors int
	selectorField        int
	datatypeMatch        *dynamicDatatypeMatch
}

type dynamicDatatypeMatch struct {
	target           smt.Term[smt.DatatypeSort]
	datatypeID       int
	constructorCount int
	branches         map[int]dynamicTerm
}

type dynamicDatatype struct {
	id               int
	constructorCount int
	sortCode         int
}

type parametricDatatypeFamily struct {
	name       string
	parameters []string
	body       List
	instances  map[string]dynamicDatatype
}

type dynamicDatatypeRecognizer struct {
	datatypeID       int
	constructorCount int
	constructorID    int
	sortCode         int
	recursive        bool
	witness          smt.RecursiveDatatypeConstructor
	binaryWitness    smt.BinaryRecursiveDatatypeConstructor
	naryWitness      smt.NaryRecursiveDatatypeConstructor
	mixedWitness     smt.MixedRecursiveDatatypeConstructor
	mixed            bool
	arity            int
}

type dynamicRecursiveDatatypeConstructor struct {
	witness       smt.RecursiveDatatypeConstructor
	binaryWitness smt.BinaryRecursiveDatatypeConstructor
	naryWitness   smt.NaryRecursiveDatatypeConstructor
	mixedWitness  smt.MixedRecursiveDatatypeConstructor
	fieldSorts    []datatypeFieldSort
	datatypeID    int
	constructors  int
	constructorID int
	name          string
	sortCode      int
	arity         int
	field         int
}

type datatypeConstructorDeclaration struct {
	name          string
	selectorNames []string
	fieldSorts    []datatypeFieldSort
	arity         int
}

type datatypeFieldSort struct {
	sort         int
	width        int
	datatypeID   int
	constructors int
}

type dynamicUnaryFunction struct {
	domain         int
	rangeSort      int
	value          smt.UnaryFunction
	real           bool
	realValue      smt.SortedUnaryFunction[smt.RealSort, smt.RealSort]
	integer        bool
	integerValue   smt.SortedUnaryFunction[smt.IntSort, smt.IntSort]
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
	integer        bool
	integerValue   smt.SortedBinaryFunction[smt.IntSort, smt.IntSort, smt.IntSort]
	bitVector      bool
	firstWidth     int
	secondWidth    int
	rangeWidth     int
	bitVectorValue smt.SortedBinaryFunction[smt.BitVecSort, smt.BitVecSort, smt.BitVecSort]
}

type dynamicTernaryFunction struct {
	integerValue smt.SortedTernaryFunction[smt.IntSort, smt.IntSort, smt.IntSort, smt.IntSort]
}

type executor struct {
	solver                 smt.Solver
	checkpoints            []smt.Checkpoint
	booleans               map[string]smt.Term[smt.BoolSort]
	integers               map[string]smt.Term[smt.IntSort]
	reals                  map[string]smt.Term[smt.RealSort]
	bitVectors             map[string]dynamicTerm
	strings                map[string]smt.Term[smt.StringSort]
	arrays                 map[string]dynamicTerm
	uninterpreted          map[string]dynamicTerm
	sorts                  map[string]int
	functions              map[string]dynamicUnaryFunction
	binaryFunctions        map[string]dynamicBinaryFunction
	ternaryFunctions       map[string]dynamicTernaryFunction
	datatypes              map[string]dynamicDatatype
	datatypeTerms          map[string]dynamicTerm
	datatypeRecognizers    map[string]dynamicDatatypeRecognizer
	datatypeConstructors   map[string]dynamicRecursiveDatatypeConstructor
	datatypeSelectors      map[string]dynamicRecursiveDatatypeConstructor
	parametricFamilies     map[string]*parametricDatatypeFamily
	parametricConstructors map[string][]dynamicRecursiveDatatypeConstructor
	parametricSelectors    map[string][]dynamicRecursiveDatatypeConstructor
	parametricRecognizers  map[string][]dynamicDatatypeRecognizer
	localTerms             map[string]dynamicTerm
	nextSymbol             int
	nextAssertion          int
	lastModel              *smt.Model
	responses              []Response
	errors                 []ExecutionError
}

func executeCommands(commands []Command) ([]Response, []ExecutionError) {
	executor := executor{
		solver:                 smt.New(),
		booleans:               make(map[string]smt.Term[smt.BoolSort]),
		integers:               make(map[string]smt.Term[smt.IntSort]),
		reals:                  make(map[string]smt.Term[smt.RealSort]),
		bitVectors:             make(map[string]dynamicTerm),
		strings:                make(map[string]smt.Term[smt.StringSort]),
		arrays:                 make(map[string]dynamicTerm),
		uninterpreted:          make(map[string]dynamicTerm),
		sorts:                  make(map[string]int),
		functions:              make(map[string]dynamicUnaryFunction),
		binaryFunctions:        make(map[string]dynamicBinaryFunction),
		ternaryFunctions:       make(map[string]dynamicTernaryFunction),
		datatypes:              make(map[string]dynamicDatatype),
		datatypeTerms:          make(map[string]dynamicTerm),
		datatypeRecognizers:    make(map[string]dynamicDatatypeRecognizer),
		datatypeConstructors:   make(map[string]dynamicRecursiveDatatypeConstructor),
		datatypeSelectors:      make(map[string]dynamicRecursiveDatatypeConstructor),
		parametricFamilies:     make(map[string]*parametricDatatypeFamily),
		parametricConstructors: make(map[string][]dynamicRecursiveDatatypeConstructor),
		parametricSelectors:    make(map[string][]dynamicRecursiveDatatypeConstructor),
		parametricRecognizers:  make(map[string][]dynamicDatatypeRecognizer),
		localTerms:             make(map[string]dynamicTerm),
		nextAssertion:          1,
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
		if len(value.Domain) == 3 {
			executor.declareTernary(index, value)
			return
		}
		if len(value.Domain) != 0 {
			executor.fail(index, value.At, "only nullary through ternary declare-fun are supported")
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
			if term.datatypeMatch != nil {
				matched := term.datatypeMatch
				target, found := smt.DatatypeModelValue(matched.datatypeID, matched.constructorCount, *executor.lastModel, matched.target)
				selected, branchFound := matched.branches[target.ConstructorID]
				if !found || !branchFound {
					values[valueIndex] = UnavailableValue{Expression: expression, Reason: "model has no datatype match value"}
					continue
				}
				term = selected
			}
			if term.datatype != nil {
				result, found := smt.DatatypeModelValue(term.datatypeID, term.constructorCount, *executor.lastModel, term.datatype)
				if found {
					values[valueIndex] = DatatypeValue{Expression: expression, Value: result}
				} else {
					values[valueIndex] = UnavailableValue{Expression: expression, Reason: "model has no datatype value"}
				}
			} else if term.selectorTarget != nil {
				target, found := smt.DatatypeModelValue(term.selectorDatatypeID, term.selectorConstructors, *executor.lastModel, term.selectorTarget)
				field, fieldFound := target.Fields.At(term.selectorField)
				if !found || !fieldFound {
					values[valueIndex] = UnavailableValue{Expression: expression, Reason: "model has no datatype selector value"}
				} else {
					switch term.sort {
					case sortBool:
						values[valueIndex] = BooleanValue{Expression: expression, Value: field.Boolean}
					case sortInt:
						if small, fits := field.Integer.Int64(); fits {
							values[valueIndex] = IntegerValue{Expression: expression, Value: small}
						} else {
							values[valueIndex] = ArbitraryIntegerValue{Expression: expression, Value: field.Integer}
						}
					case sortReal:
						values[valueIndex] = RationalValue{Expression: expression, Value: field.Real}
					case sortBitVector:
						values[valueIndex] = BitVectorValue{Expression: expression, Value: field.BitVector}
					default:
						values[valueIndex] = UnavailableValue{Expression: expression, Reason: "unsupported datatype selector value"}
					}
				}
			} else if term.sort == sortBool {
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
			} else if term.sort == sortString {
				result, found := smt.StringModelValue(*executor.lastModel, term.stringValue)
				if found {
					values[valueIndex] = StringValue{Expression: expression, Value: result}
				} else {
					values[valueIndex] = UnavailableValue{Expression: expression, Reason: "model has no string value"}
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
				if !found {
					if stringResult, stringFound := smt.ExactStringIntegerModelValue(*executor.lastModel, term.integer); stringFound {
						if small, fits := stringResult.Int64(); fits {
							values[valueIndex] = IntegerValue{Expression: expression, Value: small}
						} else {
							values[valueIndex] = ArbitraryIntegerValue{Expression: expression, Value: stringResult}
						}
						continue
					}
				}
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
		if value.Name == "declare-datatype" {
			executor.declareDatatype(index, value)
			return
		}
		if value.Name == "declare-datatypes" {
			executor.declareDatatypes(index, value)
			return
		}
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
	if _, exists := executor.strings[name]; exists {
		executor.fail(index, at, "duplicate declaration "+name)
		return
	}
	if _, exists := executor.arrays[name]; exists {
		executor.fail(index, at, "duplicate declaration "+name)
		return
	}
	if _, exists := executor.datatypeTerms[name]; exists {
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
	if datatype, ok, err := executor.instantiateParametricSort(sortExpression); ok {
		if err != nil {
			executor.fail(index, at, err.Error())
			return
		}
		executor.nextSymbol++
		executor.datatypeTerms[name] = dynamicTerm{
			sort: datatype.sortCode, datatypeID: datatype.id, constructorCount: datatype.constructorCount,
			datatype: smt.DatatypeConst(datatype.id, datatype.constructorCount, executor.nextSymbol, name),
		}
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
	case "String":
		executor.strings[name] = smt.StringConst(executor.nextSymbol, name)
	default:
		if datatype, exists := executor.datatypes[sortName]; exists {
			executor.datatypeTerms[name] = dynamicTerm{
				sort: datatype.sortCode, datatypeID: datatype.id, constructorCount: datatype.constructorCount,
				datatype: smt.DatatypeConst(datatype.id, datatype.constructorCount, executor.nextSymbol, name),
			}
			executor.acknowledge(index)
			return
		}
		sortID, exists := executor.sorts[sortName]
		if !exists {
			executor.fail(index, at, "unsupported sort "+sortName)
			return
		}
		executor.uninterpreted[name] = dynamicTerm{sort: sortID + 2, uninterpreted: smt.UninterpretedConstant(sortID, executor.nextSymbol, name)}
	}
	executor.acknowledge(index)
}

func (executor *executor) instantiateParametricSort(expression SExpr) (dynamicDatatype, bool, error) {
	application, ok := expression.(List)
	if !ok || len(application.Values) < 2 {
		return dynamicDatatype{}, false, nil
	}
	name, nameOK := atomText(application.Values[0])
	if !nameOK {
		return dynamicDatatype{}, false, nil
	}
	family, found := executor.parametricFamilies[name]
	if !found {
		return dynamicDatatype{}, false, nil
	}
	if len(application.Values)-1 != len(family.parameters) {
		return dynamicDatatype{}, true, fmt.Errorf("parametric datatype %s requires %d type arguments", name, len(family.parameters))
	}
	arguments := make([]datatypeFieldSort, len(family.parameters))
	for index, expression := range application.Values[1:] {
		argument, argumentOK := executor.parametricSortArgument(expression)
		if !argumentOK {
			return dynamicDatatype{}, true, fmt.Errorf("unsupported type argument %d for parametric datatype %s", index, name)
		}
		arguments[index] = argument
	}
	key := parametricSortKey(arguments)
	if datatype, exists := family.instances[key]; exists {
		return datatype, true, nil
	}
	executor.nextSymbol++
	datatype := dynamicDatatype{id: executor.nextSymbol, constructorCount: len(family.body.Values), sortCode: sortDatatypeBase - executor.nextSymbol}
	// Publish the identity before resolving fields. Cross-family references in
	// a mutually parametric group can then close a cycle without recursively
	// allocating a second identity for the same concrete instantiation.
	family.instances[key] = datatype
	declarations := make([]datatypeConstructorDeclaration, len(family.body.Values))
	seenConstructors := make(map[string]struct{}, len(family.body.Values))
	seenSelectors := make(map[string]struct{})
	for constructorIndex, expression := range family.body.Values {
		entry, entryOK := expression.(List)
		if !entryOK || len(entry.Values) == 0 {
			return dynamicDatatype{}, true, fmt.Errorf("datatype constructor must be a nonempty list")
		}
		constructorName, constructorOK := atomText(entry.Values[0])
		if !constructorOK {
			return dynamicDatatype{}, true, fmt.Errorf("datatype constructor name must be a symbol")
		}
		if _, duplicate := seenConstructors[constructorName]; duplicate {
			return dynamicDatatype{}, true, fmt.Errorf("duplicate datatype constructor %s", constructorName)
		}
		if _, conflict := seenSelectors[constructorName]; conflict {
			return dynamicDatatype{}, true, fmt.Errorf("datatype constructor conflicts with selector %s", constructorName)
		}
		seenConstructors[constructorName] = struct{}{}
		constructor := &declarations[constructorIndex]
		constructor.name, constructor.arity = constructorName, len(entry.Values)-1
		constructor.selectorNames = make([]string, constructor.arity)
		constructor.fieldSorts = make([]datatypeFieldSort, constructor.arity)
		for fieldIndex, fieldExpression := range entry.Values[1:] {
			field, fieldOK := fieldExpression.(List)
			if !fieldOK || len(field.Values) != 2 {
				return dynamicDatatype{}, true, fmt.Errorf("datatype field requires a selector and sort")
			}
			selector, selectorOK := atomText(field.Values[0])
			fieldSort, sortOK := executor.instantiateParametricFieldSort(field.Values[1], family, application.Values[1:], arguments, datatype)
			if !selectorOK || !sortOK {
				return dynamicDatatype{}, true, fmt.Errorf("unsupported parametric datatype field sort")
			}
			if _, duplicate := seenSelectors[selector]; duplicate {
				return dynamicDatatype{}, true, fmt.Errorf("duplicate datatype selector %s", selector)
			}
			if _, conflict := seenConstructors[selector]; conflict {
				return dynamicDatatype{}, true, fmt.Errorf("datatype selector conflicts with constructor %s", selector)
			}
			seenSelectors[selector] = struct{}{}
			constructor.selectorNames[fieldIndex], constructor.fieldSorts[fieldIndex] = selector, fieldSort
		}
	}
	productive := false
	for _, constructor := range declarations {
		ready := true
		for _, field := range constructor.fieldSorts {
			if field.sort == sortDatatypeSelf {
				ready = false
				break
			}
		}
		if ready {
			productive = true
			break
		}
	}
	if !productive {
		return dynamicDatatype{}, true, fmt.Errorf("parametric datatype %s is uninhabited", family.name)
	}
	executor.installParametricDatatypeConstructors(datatype, declarations)
	return datatype, true, nil
}

func (executor *executor) parametricSortArgument(expression SExpr) (datatypeFieldSort, bool) {
	if name, ok := atomText(expression); ok {
		switch name {
		case "Bool":
			return datatypeFieldSort{sort: sortBool}, true
		case "Int":
			return datatypeFieldSort{sort: sortInt}, true
		case "Real":
			return datatypeFieldSort{sort: sortReal}, true
		}
		if datatype, found := executor.datatypes[name]; found {
			return datatypeFieldSort{sort: datatype.sortCode, datatypeID: datatype.id, constructors: datatype.constructorCount}, true
		}
	}
	if width, ok := bitVectorSortWidth(expression); ok {
		return datatypeFieldSort{sort: sortBitVector, width: width}, true
	}
	if datatype, ok, err := executor.instantiateParametricSort(expression); ok && err == nil {
		return datatypeFieldSort{sort: datatype.sortCode, datatypeID: datatype.id, constructors: datatype.constructorCount}, true
	}
	return datatypeFieldSort{}, false
}

func parametricSortKey(sorts []datatypeFieldSort) string {
	var key strings.Builder
	for _, sort := range sorts {
		fmt.Fprintf(&key, "%d/%d/%d/%d;", sort.sort, sort.width, sort.datatypeID, sort.constructors)
	}
	return key.String()
}

func (executor *executor) instantiateParametricFieldSort(expression SExpr, family *parametricDatatypeFamily, argumentExpressions []SExpr, arguments []datatypeFieldSort, datatype dynamicDatatype) (datatypeFieldSort, bool) {
	if name, ok := atomText(expression); ok {
		for index, parameter := range family.parameters {
			if name == parameter {
				return arguments[index], true
			}
		}
		return parseDatatypeFieldSort(expression, family.name, executor.datatypes)
	}
	application, ok := expression.(List)
	if ok && len(application.Values) == len(family.parameters)+1 {
		name, nameOK := atomText(application.Values[0])
		if nameOK && name == family.name {
			for index, argument := range application.Values[1:] {
				parameter, parameterOK := atomText(argument)
				if !parameterOK || parameter != family.parameters[index] {
					return datatypeFieldSort{}, false
				}
			}
			return datatypeFieldSort{sort: sortDatatypeSelf, datatypeID: datatype.id, constructors: datatype.constructorCount}, true
		}
	}
	if ok && len(application.Values) > 0 {
		if name, nameOK := atomText(application.Values[0]); nameOK && name == family.name {
			// Non-regular recursion changes the instantiation at every edge
			// and cannot be represented by one finite monomorphized sort.
			return datatypeFieldSort{}, false
		}
	}
	substituted, changed := substituteParametricSortExpression(expression, family.parameters, argumentExpressions)
	if changed {
		if nested, ok, err := executor.instantiateParametricSort(substituted); ok && err == nil {
			return datatypeFieldSort{sort: nested.sortCode, datatypeID: nested.id, constructors: nested.constructorCount}, true
		}
	}
	return datatypeFieldSort{}, false
}

func substituteParametricSortExpression(expression SExpr, parameters []string, arguments []SExpr) (SExpr, bool) {
	if name, ok := atomText(expression); ok {
		for index, parameter := range parameters {
			if name == parameter {
				return arguments[index], true
			}
		}
		return expression, false
	}
	list, ok := expression.(List)
	if !ok {
		return expression, false
	}
	values := make([]SExpr, len(list.Values))
	changed := false
	for index, item := range list.Values {
		values[index], ok = substituteParametricSortExpression(item, parameters, arguments)
		changed = changed || ok
	}
	if !changed {
		return expression, false
	}
	list.Values = values
	return list, true
}

func (executor *executor) declareDatatype(index int, declaration RawCommand) {
	if len(declaration.Arguments) != 2 {
		executor.fail(index, declaration.At, "declare-datatype requires a sort name and constructor list")
		return
	}
	name, nameOK := atomText(declaration.Arguments[0])
	constructors, constructorsOK := declaration.Arguments[1].(List)
	if !nameOK || !constructorsOK || len(constructors.Values) == 0 {
		executor.fail(index, declaration.At, "finite declare-datatype requires at least one nullary constructor")
		return
	}
	if _, exists := executor.sorts[name]; exists {
		executor.fail(index, declaration.At, "duplicate sort declaration "+name)
		return
	}
	if _, exists := executor.datatypes[name]; exists || name == "Bool" || name == "Int" || name == "Real" {
		executor.fail(index, declaration.At, "duplicate sort declaration "+name)
		return
	}
	constructorDeclarations := make([]datatypeConstructorDeclaration, len(constructors.Values))
	seenConstructors := make(map[string]struct{}, len(constructors.Values))
	seenSelectors := make(map[string]struct{}, len(constructors.Values))
	hasBaseConstructor := false
	for constructorIndex, expression := range constructors.Values {
		entry, ok := expression.(List)
		if !ok || len(entry.Values) < 1 {
			executor.fail(index, declaration.At, "datatype constructor must be a nonempty list")
			return
		}
		constructorName, ok := atomText(entry.Values[0])
		if !ok {
			executor.fail(index, declaration.At, "datatype constructor name must be a symbol")
			return
		}
		if _, exists := executor.datatypeTerms[constructorName]; exists {
			executor.fail(index, declaration.At, "duplicate datatype constructor "+constructorName)
			return
		}
		if _, exists := executor.datatypeConstructors[constructorName]; exists {
			executor.fail(index, declaration.At, "duplicate datatype constructor "+constructorName)
			return
		}
		if _, exists := seenConstructors[constructorName]; exists {
			executor.fail(index, declaration.At, "duplicate datatype constructor "+constructorName)
			return
		}
		if _, exists := seenSelectors[constructorName]; exists {
			executor.fail(index, declaration.At, "datatype constructor conflicts with selector "+constructorName)
			return
		}
		seenConstructors[constructorName] = struct{}{}
		constructorDeclarations[constructorIndex].name = constructorName
		if len(entry.Values) > 1 {
			constructorDeclarations[constructorIndex].arity = len(entry.Values) - 1
			constructorDeclarations[constructorIndex].selectorNames = make([]string, len(entry.Values)-1)
			constructorDeclarations[constructorIndex].fieldSorts = make([]datatypeFieldSort, len(entry.Values)-1)
			for fieldIndex, fieldExpression := range entry.Values[1:] {
				field, ok := fieldExpression.(List)
				if !ok || len(field.Values) != 2 {
					executor.fail(index, declaration.At, "recursive datatype field requires a selector and its datatype sort")
					return
				}
				selectorName, selectorOK := atomText(field.Values[0])
				fieldSort, sortOK := parseDatatypeFieldSort(field.Values[1], name, executor.datatypes)
				if !selectorOK || !sortOK {
					executor.fail(index, declaration.At, "datatype field must use Bool, Int, Real, (_ BitVec n), or the enclosing sort "+name)
					return
				}
				if _, exists := seenSelectors[selectorName]; exists {
					executor.fail(index, declaration.At, "duplicate datatype selector "+selectorName)
					return
				}
				if _, exists := executor.datatypeSelectors[selectorName]; exists {
					executor.fail(index, declaration.At, "duplicate datatype selector "+selectorName)
					return
				}
				if _, exists := seenConstructors[selectorName]; exists {
					executor.fail(index, declaration.At, "datatype selector conflicts with constructor "+selectorName)
					return
				}
				seenSelectors[selectorName] = struct{}{}
				constructorDeclarations[constructorIndex].selectorNames[fieldIndex] = selectorName
				constructorDeclarations[constructorIndex].fieldSorts[fieldIndex] = fieldSort
			}
		} else {
			hasBaseConstructor = true
		}
	}
	recursive := false
	for _, constructor := range constructorDeclarations {
		for _, field := range constructor.fieldSorts {
			recursive = recursive || field.sort == sortDatatypeSelf
		}
	}
	if recursive && !hasBaseConstructor {
		executor.fail(index, declaration.At, "recursive datatype requires at least one nullary base constructor")
		return
	}
	executor.nextSymbol++
	datatypeID := executor.nextSymbol
	datatype := dynamicDatatype{id: datatypeID, constructorCount: len(constructorDeclarations), sortCode: sortDatatypeBase - datatypeID}
	executor.datatypes[name] = datatype
	for constructorID, constructor := range constructorDeclarations {
		if constructor.arity == 0 {
			executor.datatypeTerms[constructor.name] = dynamicTerm{
				sort: datatype.sortCode, datatypeID: datatype.id, constructorCount: datatype.constructorCount,
				datatype: smt.DatatypeConstructor(datatype.id, datatype.constructorCount, constructorID, constructor.name),
			}
		} else if !allDatatypeFieldsSelf(constructor.fieldSorts, datatype.sortCode) {
			witness := declareDynamicMixedDatatypeConstructor(datatype, constructorID, constructor)
			dynamic := dynamicRecursiveDatatypeConstructor{mixedWitness: witness, fieldSorts: constructor.fieldSorts, datatypeID: datatype.id, constructors: datatype.constructorCount, sortCode: datatype.sortCode, arity: constructor.arity}
			executor.datatypeConstructors[constructor.name] = dynamic
			for field, selectorName := range constructor.selectorNames {
				selector := dynamic
				selector.field = field
				executor.datatypeSelectors[selectorName] = selector
			}
		} else if constructor.arity == 1 {
			witness := smt.DeclareRecursiveDatatypeConstructor(datatype.id, datatype.constructorCount, constructorID, constructor.name, constructor.selectorNames[0])
			dynamic := dynamicRecursiveDatatypeConstructor{witness: witness, sortCode: datatype.sortCode, arity: 1}
			executor.datatypeConstructors[constructor.name] = dynamic
			executor.datatypeSelectors[constructor.selectorNames[0]] = dynamic
		} else if constructor.arity == 2 {
			witness := smt.DeclareBinaryRecursiveDatatypeConstructor(datatype.id, datatype.constructorCount, constructorID, constructor.name, constructor.selectorNames[0], constructor.selectorNames[1])
			dynamic := dynamicRecursiveDatatypeConstructor{binaryWitness: witness, sortCode: datatype.sortCode, arity: 2}
			executor.datatypeConstructors[constructor.name] = dynamic
			first, second := dynamic, dynamic
			first.field, second.field = 0, 1
			executor.datatypeSelectors[constructor.selectorNames[0]] = first
			executor.datatypeSelectors[constructor.selectorNames[1]] = second
		} else {
			witness := smt.DeclareNaryRecursiveDatatypeConstructorCompact(datatype.id, datatype.constructorCount, constructorID, constructor.name, compactDatatypeSelectors(constructor.selectorNames))
			dynamic := dynamicRecursiveDatatypeConstructor{naryWitness: witness, sortCode: datatype.sortCode, arity: constructor.arity}
			executor.datatypeConstructors[constructor.name] = dynamic
			for field, selectorName := range constructor.selectorNames {
				selector := dynamic
				selector.field = field
				executor.datatypeSelectors[selectorName] = selector
			}
		}
		executor.datatypeRecognizers["is-"+constructor.name] = dynamicDatatypeRecognizer{
			datatypeID: datatype.id, constructorCount: datatype.constructorCount, constructorID: constructorID, sortCode: datatype.sortCode,
		}
		if constructor.arity != 0 {
			recognizer := executor.datatypeRecognizers["is-"+constructor.name]
			recognizer.recursive = true
			recognizer.arity = constructor.arity
			recognizer.witness = executor.datatypeConstructors[constructor.name].witness
			recognizer.binaryWitness = executor.datatypeConstructors[constructor.name].binaryWitness
			recognizer.naryWitness = executor.datatypeConstructors[constructor.name].naryWitness
			recognizer.mixedWitness = executor.datatypeConstructors[constructor.name].mixedWitness
			recognizer.mixed = len(executor.datatypeConstructors[constructor.name].fieldSorts) != 0
			executor.datatypeRecognizers["is-"+constructor.name] = recognizer
		}
	}
	executor.acknowledge(index)
}

func (executor *executor) declareDatatypes(index int, declaration RawCommand) {
	if len(declaration.Arguments) != 2 {
		executor.fail(index, declaration.At, "declare-datatypes requires sort declarations and constructor lists")
		return
	}
	sorts, sortsOK := declaration.Arguments[0].(List)
	bodies, bodiesOK := declaration.Arguments[1].(List)
	if !sortsOK || !bodiesOK || len(sorts.Values) == 0 || len(sorts.Values) != len(bodies.Values) {
		executor.fail(index, declaration.At, "declare-datatypes requires one constructor list per sort")
		return
	}
	if executor.declareParametricDatatypeGroup(index, declaration.At, sorts, bodies) {
		return
	}
	names := make([]string, len(sorts.Values))
	group := make(map[string]dynamicDatatype, len(names))
	for sortIndex, expression := range sorts.Values {
		entry, ok := expression.(List)
		if !ok || len(entry.Values) != 2 {
			executor.fail(index, declaration.At, "datatype sort declaration must be (name 0)")
			return
		}
		name, nameOK := atomText(entry.Values[0])
		arity, arityOK := atomText(entry.Values[1])
		if !nameOK || !arityOK || arity != "0" {
			executor.fail(index, declaration.At, "only non-parametric datatype sort declarations are supported")
			return
		}
		_, groupDuplicate := group[name]
		_, existingDatatype := executor.datatypes[name]
		if groupDuplicate || existingDatatype || name == "Bool" || name == "Int" || name == "Real" {
			executor.fail(index, declaration.At, "duplicate sort declaration "+name)
			return
		}
		constructors, ok := bodies.Values[sortIndex].(List)
		if !ok || len(constructors.Values) == 0 {
			executor.fail(index, declaration.At, "datatype requires at least one constructor")
			return
		}
		executor.nextSymbol++
		datatype := dynamicDatatype{id: executor.nextSymbol, constructorCount: len(constructors.Values), sortCode: sortDatatypeBase - executor.nextSymbol}
		names[sortIndex], group[name] = name, datatype
	}
	declarations := make([][]datatypeConstructorDeclaration, len(names))
	seenConstructors := make(map[string]struct{})
	seenSelectors := make(map[string]struct{})
	for sortIndex, name := range names {
		body := bodies.Values[sortIndex].(List)
		declarations[sortIndex] = make([]datatypeConstructorDeclaration, len(body.Values))
		for constructorIndex, expression := range body.Values {
			entry, ok := expression.(List)
			if !ok || len(entry.Values) == 0 {
				executor.fail(index, declaration.At, "datatype constructor must be a nonempty list")
				return
			}
			constructorName, ok := atomText(entry.Values[0])
			if !ok {
				executor.fail(index, declaration.At, "datatype constructor name must be a symbol")
				return
			}
			_, duplicateConstructor := seenConstructors[constructorName]
			_, conflictsSelector := seenSelectors[constructorName]
			_, existingTerm := executor.datatypeTerms[constructorName]
			_, existingConstructor := executor.datatypeConstructors[constructorName]
			if duplicateConstructor || conflictsSelector || existingTerm || existingConstructor {
				executor.fail(index, declaration.At, "duplicate datatype constructor "+constructorName)
				return
			}
			seenConstructors[constructorName] = struct{}{}
			constructor := &declarations[sortIndex][constructorIndex]
			constructor.name, constructor.arity = constructorName, len(entry.Values)-1
			if constructor.arity == 0 {
				continue
			}
			constructor.selectorNames = make([]string, constructor.arity)
			constructor.fieldSorts = make([]datatypeFieldSort, constructor.arity)
			for fieldIndex, fieldExpression := range entry.Values[1:] {
				field, ok := fieldExpression.(List)
				if !ok || len(field.Values) != 2 {
					executor.fail(index, declaration.At, "datatype field requires a selector and sort")
					return
				}
				selector, selectorOK := atomText(field.Values[0])
				fieldSort, sortOK := parseDatatypeFieldSort(field.Values[1], name, group)
				if !selectorOK || !sortOK {
					executor.fail(index, declaration.At, "unsupported mutually recursive datatype field sort")
					return
				}
				if _, duplicate := seenSelectors[selector]; duplicate {
					executor.fail(index, declaration.At, "duplicate datatype selector "+selector)
					return
				}
				if _, conflict := seenConstructors[selector]; conflict {
					executor.fail(index, declaration.At, "datatype selector conflicts with constructor "+selector)
					return
				}
				if _, duplicate := executor.datatypeSelectors[selector]; duplicate {
					executor.fail(index, declaration.At, "duplicate datatype selector "+selector)
					return
				}
				seenSelectors[selector] = struct{}{}
				constructor.selectorNames[fieldIndex], constructor.fieldSorts[fieldIndex] = selector, fieldSort
			}
		}
	}
	productive := make(map[int]bool, len(names))
	for changed := true; changed; {
		changed = false
		for sortIndex, name := range names {
			datatype := group[name]
			if productive[datatype.sortCode] {
				continue
			}
			for _, constructor := range declarations[sortIndex] {
				ready := true
				for _, field := range constructor.fieldSorts {
					target := field.sort
					if target == sortDatatypeSelf {
						target = datatype.sortCode
					}
					if target <= sortDatatypeBase && !productive[target] {
						ready = false
						break
					}
				}
				if ready {
					productive[datatype.sortCode], changed = true, true
					break
				}
			}
		}
	}
	for _, name := range names {
		if !productive[group[name].sortCode] {
			executor.fail(index, declaration.At, "mutually recursive datatype group has an uninhabited sort "+name)
			return
		}
	}
	for _, name := range names {
		executor.datatypes[name] = group[name]
	}
	for sortIndex, name := range names {
		executor.installDatatypeConstructors(group[name], declarations[sortIndex])
	}
	executor.acknowledge(index)
}

func (executor *executor) declareParametricDatatypeGroup(index int, at Span, sorts, bodies List) bool {
	arities := make([]int, len(sorts.Values))
	names := make([]string, len(sorts.Values))
	parameterized := false
	for sortIndex, expression := range sorts.Values {
		declaration, ok := expression.(List)
		if !ok || len(declaration.Values) != 2 {
			return false
		}
		name, nameOK := atomText(declaration.Values[0])
		arityText, arityOK := atomText(declaration.Values[1])
		arity, err := strconv.Atoi(arityText)
		if !nameOK || !arityOK || err != nil || arity < 0 {
			return false
		}
		names[sortIndex], arities[sortIndex] = name, arity
		parameterized = parameterized || arity > 0
	}
	if !parameterized {
		return false
	}
	for _, arity := range arities {
		if arity == 0 {
			executor.fail(index, at, "parametric datatype groups cannot mix zero-arity and parameterized sorts")
			return true
		}
	}
	groupNames := make(map[string]struct{}, len(names))
	families := make([]*parametricDatatypeFamily, len(names))
	for sortIndex, name := range names {
		if _, duplicate := groupNames[name]; duplicate {
			executor.fail(index, at, "duplicate sort declaration "+name)
			return true
		}
		groupNames[name] = struct{}{}
		if _, exists := executor.parametricFamilies[name]; exists {
			executor.fail(index, at, "duplicate sort declaration "+name)
			return true
		}
		if _, exists := executor.datatypes[name]; exists || name == "Bool" || name == "Int" || name == "Real" {
			executor.fail(index, at, "duplicate sort declaration "+name)
			return true
		}
		family, err := parseParametricDatatypeFamily(name, arities[sortIndex], bodies.Values[sortIndex])
		if err != nil {
			executor.fail(index, at, err.Error())
			return true
		}
		families[sortIndex] = family
	}
	if len(names) > 1 {
		if unproductive := unproductiveParametricFamily(names, families, groupNames); unproductive != "" {
			executor.fail(index, at, "mutually parametric datatype group has an uninhabited sort "+unproductive)
			return true
		}
	}
	for index, name := range names {
		executor.parametricFamilies[name] = families[index]
	}
	executor.acknowledge(index)
	return true
}

func parseParametricDatatypeFamily(name string, parameterCount int, bodyExpression SExpr) (*parametricDatatypeFamily, error) {
	body, bodyOK := bodyExpression.(List)
	if !bodyOK || len(body.Values) != 3 {
		return nil, fmt.Errorf("parametric datatype body must be (par (T ...) constructors)")
	}
	par, parOK := atomText(body.Values[0])
	parameters, parametersOK := body.Values[1].(List)
	constructors, constructorsOK := body.Values[2].(List)
	if !parOK || par != "par" || !parametersOK || len(parameters.Values) != parameterCount || !constructorsOK || len(constructors.Values) == 0 {
		return nil, fmt.Errorf("parametric datatype parameter count must match its declared arity")
	}
	parameterNames := make([]string, parameterCount)
	seenParameters := make(map[string]struct{}, parameterCount)
	for parameterIndex, expression := range parameters.Values {
		parameter, parameterOK := atomText(expression)
		if !parameterOK {
			return nil, fmt.Errorf("parametric datatype parameter must be a symbol")
		}
		if _, duplicate := seenParameters[parameter]; duplicate {
			return nil, fmt.Errorf("duplicate parametric datatype parameter %s", parameter)
		}
		seenParameters[parameter] = struct{}{}
		parameterNames[parameterIndex] = parameter
	}
	return &parametricDatatypeFamily{
		name: name, parameters: parameterNames, body: constructors, instances: make(map[string]dynamicDatatype),
	}, nil
}

func unproductiveParametricFamily(names []string, families []*parametricDatatypeFamily, groupNames map[string]struct{}) string {
	productive := make(map[string]bool, len(names))
	for changed := true; changed; {
		changed = false
		for familyIndex, family := range families {
			if productive[names[familyIndex]] {
				continue
			}
			for _, constructorExpression := range family.body.Values {
				constructor, ok := constructorExpression.(List)
				if !ok || len(constructor.Values) == 0 {
					continue
				}
				ready := true
				for _, fieldExpression := range constructor.Values[1:] {
					field, ok := fieldExpression.(List)
					if !ok || len(field.Values) != 2 {
						ready = false
						break
					}
					if dependency := parametricGroupDependency(field.Values[1], groupNames); dependency != "" && !productive[dependency] {
						ready = false
						break
					}
				}
				if ready {
					productive[names[familyIndex]], changed = true, true
					break
				}
			}
		}
	}
	for _, name := range names {
		if !productive[name] {
			return name
		}
	}
	return ""
}

func parametricGroupDependency(expression SExpr, groupNames map[string]struct{}) string {
	application, ok := expression.(List)
	if !ok || len(application.Values) == 0 {
		return ""
	}
	name, ok := atomText(application.Values[0])
	if !ok {
		return ""
	}
	if _, dependency := groupNames[name]; dependency {
		return name
	}
	return ""
}

func (executor *executor) installDatatypeConstructors(datatype dynamicDatatype, declarations []datatypeConstructorDeclaration) {
	for constructorID, constructor := range declarations {
		if constructor.arity == 0 {
			executor.datatypeTerms[constructor.name] = dynamicTerm{sort: datatype.sortCode, datatypeID: datatype.id, constructorCount: datatype.constructorCount, datatype: smt.DatatypeConstructor(datatype.id, datatype.constructorCount, constructorID, constructor.name)}
		} else {
			witness := declareDynamicMixedDatatypeConstructor(datatype, constructorID, constructor)
			dynamic := dynamicRecursiveDatatypeConstructor{mixedWitness: witness, fieldSorts: constructor.fieldSorts, datatypeID: datatype.id, constructors: datatype.constructorCount, sortCode: datatype.sortCode, arity: constructor.arity}
			executor.datatypeConstructors[constructor.name] = dynamic
			for field, selectorName := range constructor.selectorNames {
				selector := dynamic
				selector.field = field
				executor.datatypeSelectors[selectorName] = selector
			}
		}
		executor.datatypeRecognizers["is-"+constructor.name] = dynamicDatatypeRecognizer{datatypeID: datatype.id, constructorCount: datatype.constructorCount, constructorID: constructorID, sortCode: datatype.sortCode}
		if constructor.arity != 0 {
			recognizer := executor.datatypeRecognizers["is-"+constructor.name]
			recognizer.recursive, recognizer.mixed, recognizer.arity = true, true, constructor.arity
			recognizer.mixedWitness = executor.datatypeConstructors[constructor.name].mixedWitness
			executor.datatypeRecognizers["is-"+constructor.name] = recognizer
		}
	}
}

func (executor *executor) installParametricDatatypeConstructors(datatype dynamicDatatype, declarations []datatypeConstructorDeclaration) {
	for constructorID, constructor := range declarations {
		if constructor.arity == 0 {
			executor.parametricConstructors[constructor.name] = append(executor.parametricConstructors[constructor.name],
				dynamicRecursiveDatatypeConstructor{datatypeID: datatype.id, constructors: datatype.constructorCount, constructorID: constructorID, name: constructor.name, sortCode: datatype.sortCode})
		} else {
			witness := declareDynamicMixedDatatypeConstructor(datatype, constructorID, constructor)
			dynamic := dynamicRecursiveDatatypeConstructor{
				mixedWitness: witness, fieldSorts: constructor.fieldSorts, datatypeID: datatype.id,
				constructors: datatype.constructorCount, constructorID: constructorID, name: constructor.name,
				sortCode: datatype.sortCode, arity: constructor.arity,
			}
			executor.parametricConstructors[constructor.name] = append(executor.parametricConstructors[constructor.name], dynamic)
			for field, selectorName := range constructor.selectorNames {
				selector := dynamic
				selector.field = field
				executor.parametricSelectors[selectorName] = append(executor.parametricSelectors[selectorName], selector)
			}
		}
		recognizer := dynamicDatatypeRecognizer{
			datatypeID: datatype.id, constructorCount: datatype.constructorCount, constructorID: constructorID,
			sortCode: datatype.sortCode, recursive: constructor.arity != 0, mixed: constructor.arity != 0,
			arity: constructor.arity,
		}
		if constructor.arity != 0 {
			recognizer.mixedWitness = executor.parametricConstructors[constructor.name][len(executor.parametricConstructors[constructor.name])-1].mixedWitness
		}
		executor.parametricRecognizers["is-"+constructor.name] = append(executor.parametricRecognizers["is-"+constructor.name], recognizer)
	}
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
	if _, exists := executor.ternaryFunctions[declaration.Name]; exists {
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
	if domainOK && rangeOK && domainName == "Int" && rangeName == "Int" {
		executor.nextSymbol++
		executor.functions[declaration.Name] = dynamicUnaryFunction{
			integer: true, integerValue: smt.DeclareIntUnaryFunction(executor.nextSymbol, declaration.Name),
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
	if _, exists := executor.ternaryFunctions[declaration.Name]; exists {
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
	if firstOK && secondOK && rangeOK && firstName == "Int" && secondName == "Int" && rangeName == "Int" {
		executor.nextSymbol++
		executor.binaryFunctions[declaration.Name] = dynamicBinaryFunction{
			integer: true, integerValue: smt.DeclareIntBinaryFunction(executor.nextSymbol, declaration.Name),
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

func (executor *executor) declareTernary(index int, declaration DeclareFun) {
	if _, exists := executor.functions[declaration.Name]; exists {
		executor.fail(index, declaration.At, "duplicate function declaration "+declaration.Name)
		return
	}
	if _, exists := executor.binaryFunctions[declaration.Name]; exists {
		executor.fail(index, declaration.At, "duplicate function declaration "+declaration.Name)
		return
	}
	if _, exists := executor.ternaryFunctions[declaration.Name]; exists {
		executor.fail(index, declaration.At, "duplicate function declaration "+declaration.Name)
		return
	}
	first, firstOK := atomText(declaration.Domain[0])
	second, secondOK := atomText(declaration.Domain[1])
	third, thirdOK := atomText(declaration.Domain[2])
	rangeName, rangeOK := atomText(declaration.Range)
	if !firstOK || !secondOK || !thirdOK || !rangeOK ||
		first != "Int" || second != "Int" || third != "Int" ||
		rangeName != "Int" {
		executor.fail(index, declaration.At, "ternary functions currently require Int arguments and Int range")
		return
	}
	executor.nextSymbol++
	executor.ternaryFunctions[declaration.Name] = dynamicTernaryFunction{
		integerValue: smt.DeclareIntTernaryFunction(executor.nextSymbol, declaration.Name),
	}
	executor.acknowledge(index)
}

func (executor *executor) term(expression SExpr) (dynamicTerm, error) {
	if atom, ok := expression.(Atom); ok {
		if _, literal := atom.Kind.(StringAtom); literal {
			return dynamicTerm{sort: sortString, stringValue: smt.StringVal(atom.Text)}, nil
		}
		switch atom.Text {
		case "true":
			return dynamicTerm{sort: sortBool, boolean: smt.Bool{Value: true}}, nil
		case "false":
			return dynamicTerm{sort: sortBool, boolean: smt.Bool{Value: false}}, nil
		case "re.none":
			return dynamicTerm{sort: sortRegexString, regexString: smt.EmptyRegex[smt.StringSort]()}, nil
		case "re.all":
			return dynamicTerm{sort: sortRegexString, regexString: smt.FullRegex[smt.StringSort]()}, nil
		case "re.allchar":
			return dynamicTerm{sort: sortRegexString, regexString: smt.AllCharRegex[smt.StringSort]()}, nil
		}
		if value, found := executor.localTerms[atom.Text]; found {
			return value, nil
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
		if value, found := executor.strings[atom.Text]; found {
			return dynamicTerm{sort: sortString, stringValue: value}, nil
		}
		if value, found := executor.arrays[atom.Text]; found {
			return value, nil
		}
		if value, found := executor.datatypeTerms[atom.Text]; found {
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
	if character, recognized, err := indexedCharacterConstant(list); recognized {
		if err != nil {
			return dynamicTerm{}, err
		}
		return dynamicTerm{sort: sortString, stringValue: character}, nil
	}
	if operator, operatorOK := atomText(list.Values[0]); operatorOK && operator == "match" {
		return executor.matchParametricDatatype(list)
	}
	if len(list.Values) == 3 {
		if qualifier, qualifierOK := atomText(list.Values[0]); qualifierOK && qualifier == "as" {
			constructorName, constructorOK := atomText(list.Values[1])
			if constructorOK && isStringRegexSort(list.Values[2]) {
				switch constructorName {
				case "re.none":
					return dynamicTerm{sort: sortRegexString, regexString: smt.EmptyRegex[smt.StringSort]()}, nil
				case "re.all":
					return dynamicTerm{sort: sortRegexString, regexString: smt.FullRegex[smt.StringSort]()}, nil
				case "re.allchar":
					return dynamicTerm{sort: sortRegexString, regexString: smt.AllCharRegex[smt.StringSort]()}, nil
				}
			}
			datatype, datatypeOK, err := executor.instantiateParametricSort(list.Values[2])
			if err != nil {
				return dynamicTerm{}, err
			}
			if !constructorOK || !datatypeOK {
				return dynamicTerm{}, fmt.Errorf("invalid qualified parametric datatype constructor")
			}
			for _, constructor := range executor.parametricConstructors[constructorName] {
				if constructor.sortCode == datatype.sortCode && constructor.arity == 0 {
					return dynamicTerm{
						sort: datatype.sortCode, datatypeID: datatype.id, constructorCount: datatype.constructorCount,
						datatype: smt.DatatypeConstructor(datatype.id, datatype.constructorCount, constructor.constructorID, constructor.name),
					}, nil
				}
			}
			return dynamicTerm{}, fmt.Errorf("unknown qualified datatype constructor %s", constructorName)
		}
	}
	operator, ok := atomText(list.Values[0])
	var indexedParameters []int
	constantIntArray := false
	constantBitVecArray := false
	updateSelector := ""
	constantArrayIndexWidth, constantArrayElementWidth := 0, 0
	if !ok {
		if intIntConstArrayOperator(list.Values[0]) {
			operator, ok, constantIntArray = "const-array", true, true
		} else if iw, ew, arrayOK := bitVectorConstArrayOperator(list.Values[0]); arrayOK {
			operator, ok, constantBitVecArray = "const-array", true, true
			constantArrayIndexWidth, constantArrayElementWidth = iw, ew
		} else if constructor, recognizerOK := indexedDatatypeRecognizerOperator(list.Values[0]); recognizerOK {
			operator, ok = "is-"+constructor, true
		} else if selector, updateOK := indexedDatatypeUpdateOperator(list.Values[0]); updateOK {
			operator, ok, updateSelector = "update-field", true, selector
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
	if indexedParameters != nil && (operator == "re.loop" || operator == "re.^") {
		return buildIndexedRegexApplication(operator, indexedParameters, terms)
	}
	if indexedParameters != nil {
		return buildIndexedBitVectorApplication(operator, indexedParameters, terms)
	}
	if updateSelector != "" {
		if len(terms) != 2 || terms[0].datatype == nil {
			return dynamicTerm{}, fmt.Errorf("ill-sorted datatype update-field %s", updateSelector)
		}
		if selector, found := executor.datatypeSelectors[updateSelector]; found && selector.sortCode == terms[0].sort {
			return updateDynamicMixedDatatypeField(selector, terms[0], terms[1])
		}
		for _, selector := range executor.parametricSelectors[updateSelector] {
			if selector.sortCode == terms[0].sort {
				return updateDynamicMixedDatatypeField(selector, terms[0], terms[1])
			}
		}
		return dynamicTerm{}, fmt.Errorf("unknown datatype update-field selector %s", updateSelector)
	}
	if constantIntArray {
		if len(terms) == 1 && (terms[0].sort == sortInt || terms[0].sort == sortNumber && terms[0].integer != nil) {
			return dynamicTerm{sort: sortArrayIntInt, arrayIntInt: smt.ConstArray[smt.IntSort, smt.IntSort](terms[0].integer)}, nil
		}
		return dynamicTerm{}, fmt.Errorf("ill-sorted constant integer array")
	}
	if recognizer, found := executor.datatypeRecognizers[operator]; found {
		if len(terms) != 1 || terms[0].sort != recognizer.sortCode || terms[0].datatypeID != recognizer.datatypeID || terms[0].constructorCount != recognizer.constructorCount {
			return dynamicTerm{}, fmt.Errorf("ill-sorted datatype recognizer %s", operator)
		}
		if recognizer.recursive {
			if recognizer.mixed {
				return dynamicTerm{sort: sortBool, boolean: smt.IsMixedRecursiveDatatypeConstructor(recognizer.mixedWitness, terms[0].datatype)}, nil
			}
			if recognizer.arity > 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.IsNaryRecursiveDatatypeConstructor(recognizer.naryWitness, terms[0].datatype)}, nil
			}
			if recognizer.arity == 2 {
				return dynamicTerm{sort: sortBool, boolean: smt.IsBinaryRecursiveDatatypeConstructor(recognizer.binaryWitness, terms[0].datatype)}, nil
			}
			return dynamicTerm{sort: sortBool, boolean: smt.IsRecursiveDatatypeConstructor(recognizer.witness, terms[0].datatype)}, nil
		}
		return dynamicTerm{sort: sortBool, boolean: smt.IsDatatypeConstructor(recognizer.datatypeID, recognizer.constructorCount, recognizer.constructorID, terms[0].datatype)}, nil
	}
	if recognizers := executor.parametricRecognizers[operator]; len(recognizers) != 0 {
		if len(terms) != 1 {
			return dynamicTerm{}, fmt.Errorf("ill-sorted datatype recognizer %s", operator)
		}
		for _, recognizer := range recognizers {
			if terms[0].sort != recognizer.sortCode {
				continue
			}
			if recognizer.recursive {
				return dynamicTerm{sort: sortBool, boolean: smt.IsMixedRecursiveDatatypeConstructor(recognizer.mixedWitness, terms[0].datatype)}, nil
			}
			return dynamicTerm{sort: sortBool, boolean: smt.IsDatatypeConstructor(recognizer.datatypeID, recognizer.constructorCount, recognizer.constructorID, terms[0].datatype)}, nil
		}
		return dynamicTerm{}, fmt.Errorf("ill-sorted datatype recognizer %s", operator)
	}
	if constructor, found := executor.datatypeConstructors[operator]; found {
		if int(constructor.arity) != len(terms) {
			return dynamicTerm{}, fmt.Errorf("ill-sorted datatype constructor %s", operator)
		}
		for field, term := range terms {
			if !datatypeFieldAccepts(constructor.fieldSorts, field, constructor.sortCode, term) {
				return dynamicTerm{}, fmt.Errorf("ill-sorted datatype constructor %s", operator)
			}
		}
		if len(constructor.fieldSorts) != 0 {
			arguments, ok := dynamicMixedDatatypeArguments(constructor.fieldSorts, terms)
			if !ok {
				return dynamicTerm{}, fmt.Errorf("ill-sorted datatype constructor %s", operator)
			}
			return dynamicTerm{sort: constructor.sortCode, datatypeID: constructor.datatypeID, constructorCount: constructor.constructors,
				datatype: smt.ApplyMixedRecursiveDatatypeConstructor(constructor.mixedWitness, arguments)}, nil
		}
		if constructor.arity > 2 {
			return dynamicTerm{sort: terms[0].sort, datatypeID: terms[0].datatypeID, constructorCount: terms[0].constructorCount,
				datatype: smt.ApplyNaryRecursiveDatatypeConstructorCompact(constructor.naryWitness, compactDatatypeTerms(terms))}, nil
		}
		if constructor.arity == 2 {
			return dynamicTerm{sort: terms[0].sort, datatypeID: terms[0].datatypeID, constructorCount: terms[0].constructorCount,
				datatype: smt.ApplyBinaryRecursiveDatatypeConstructor(constructor.binaryWitness, terms[0].datatype, terms[1].datatype)}, nil
		}
		return dynamicTerm{sort: terms[0].sort, datatypeID: terms[0].datatypeID, constructorCount: terms[0].constructorCount,
			datatype: smt.ApplyRecursiveDatatypeConstructor(constructor.witness, terms[0].datatype)}, nil
	}
	if constructors := executor.parametricConstructors[operator]; len(constructors) != 0 {
		for _, constructor := range constructors {
			if constructor.arity != len(terms) || constructor.arity == 0 {
				continue
			}
			matches := true
			for field, term := range terms {
				if !datatypeFieldAccepts(constructor.fieldSorts, field, constructor.sortCode, term) {
					matches = false
					break
				}
			}
			if !matches {
				continue
			}
			arguments, argumentsOK := dynamicMixedDatatypeArguments(constructor.fieldSorts, terms)
			if !argumentsOK {
				continue
			}
			return dynamicTerm{
				sort: constructor.sortCode, datatypeID: constructor.datatypeID, constructorCount: constructor.constructors,
				datatype: smt.ApplyMixedRecursiveDatatypeConstructor(constructor.mixedWitness, arguments),
			}, nil
		}
		return dynamicTerm{}, fmt.Errorf("ill-sorted or ambiguous parametric datatype constructor %s", operator)
	}
	if selector, found := executor.datatypeSelectors[operator]; found {
		if len(terms) != 1 || terms[0].sort != selector.sortCode {
			return dynamicTerm{}, fmt.Errorf("ill-sorted datatype selector %s", operator)
		}
		if len(selector.fieldSorts) != 0 {
			return selectDynamicMixedDatatypeField(selector, terms[0])
		}
		selected := terms[0].datatype
		if selector.arity > 2 {
			selected = smt.SelectNaryRecursiveDatatypeConstructorDynamic(selector.field, selector.naryWitness, terms[0].datatype)
		} else if selector.arity == 2 {
			field := smt.BinaryDatatypeField(smt.FirstDatatypeField{})
			if selector.field == 1 {
				field = smt.SecondDatatypeField{}
			}
			selected = smt.SelectBinaryRecursiveDatatypeConstructor(field, selector.binaryWitness, terms[0].datatype)
		} else {
			selected = smt.SelectRecursiveDatatypeConstructor(selector.witness, terms[0].datatype)
		}
		return dynamicTerm{sort: terms[0].sort, datatypeID: terms[0].datatypeID, constructorCount: terms[0].constructorCount, datatype: selected}, nil
	}
	if selectors := executor.parametricSelectors[operator]; len(selectors) != 0 {
		if len(terms) != 1 {
			return dynamicTerm{}, fmt.Errorf("ill-sorted datatype selector %s", operator)
		}
		for _, selector := range selectors {
			if terms[0].sort == selector.sortCode {
				return selectDynamicMixedDatatypeField(selector, terms[0])
			}
		}
		return dynamicTerm{}, fmt.Errorf("ill-sorted datatype selector %s", operator)
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
		if function.integer {
			if len(terms) != 1 || terms[0].integer == nil || terms[0].sort != sortInt && terms[0].sort != sortNumber {
				return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
			}
			return dynamicTerm{sort: sortInt, integer: smt.ApplySortedUnary(function.integerValue, terms[0].integer)}, nil
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
		if function.integer {
			if len(terms) != 2 ||
				terms[0].integer == nil || terms[0].sort != sortInt && terms[0].sort != sortNumber ||
				terms[1].integer == nil || terms[1].sort != sortInt && terms[1].sort != sortNumber {
				return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
			}
			return dynamicTerm{sort: sortInt, integer: smt.ApplySortedBinary(function.integerValue, terms[0].integer, terms[1].integer)}, nil
		}
		if len(terms) != 2 || terms[0].sort != function.first+2 || terms[1].sort != function.second+2 {
			return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
		}
		return dynamicTerm{sort: function.rangeSort + 2, uninterpreted: smt.ApplyBinary(function.value, terms[0].uninterpreted, terms[1].uninterpreted)}, nil
	}
	if function, found := executor.ternaryFunctions[operator]; found {
		if len(terms) != 3 {
			return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
		}
		for _, term := range terms {
			if term.integer == nil || term.sort != sortInt && term.sort != sortNumber {
				return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
			}
		}
		return dynamicTerm{
			sort: sortInt,
			integer: smt.ApplySortedTernary(
				function.integerValue,
				terms[0].integer, terms[1].integer, terms[2].integer,
			),
		}, nil
	}
	return buildApplication(operator, terms)
}

func indexedCharacterConstant(list List) (smt.Term[smt.StringSort], bool, error) {
	if len(list.Values) != 3 {
		return nil, false, nil
	}
	qualifier, qualifierOK := atomText(list.Values[0])
	name, nameOK := atomText(list.Values[1])
	if !qualifierOK || !nameOK || qualifier != "_" || name != "char" {
		return nil, false, nil
	}
	index, indexOK := atomText(list.Values[2])
	if !indexOK || len(index) < 3 || len(index) > 7 ||
		!strings.HasPrefix(index, "#x") {
		return nil, true, fmt.Errorf("invalid indexed character constant")
	}
	digits := index[2:]
	for _, digit := range digits {
		if !strings.ContainsRune("0123456789abcdefABCDEF", digit) {
			return nil, true, fmt.Errorf("invalid indexed character constant %s", index)
		}
	}
	value, err := strconv.ParseInt(digits, 16, 64)
	if err != nil {
		return nil, true, fmt.Errorf("invalid indexed character constant %s", index)
	}
	character, valid := smt.StringCharacter(value)
	if !valid {
		return nil, true, fmt.Errorf("indexed character constant out of range %s", index)
	}
	return character, true, nil
}

func (executor *executor) matchParametricDatatype(expression List) (dynamicTerm, error) {
	if len(expression.Values) != 3 {
		return dynamicTerm{}, fmt.Errorf("match requires a datatype scrutinee and case list")
	}
	target, err := executor.term(expression.Values[1])
	if err != nil || target.datatype == nil {
		return dynamicTerm{}, fmt.Errorf("match scrutinee must be a datatype term")
	}
	cases, ok := expression.Values[2].(List)
	if !ok || len(cases.Values) == 0 {
		return dynamicTerm{}, fmt.Errorf("match requires at least one case")
	}
	type matchBranch struct {
		constructorID int
		condition     smt.Term[smt.BoolSort]
		value         dynamicTerm
	}
	branches := make([]matchBranch, 0, len(cases.Values))
	seen := make(map[int]struct{}, len(cases.Values))
	for _, caseExpression := range cases.Values {
		entry, entryOK := caseExpression.(List)
		if !entryOK || len(entry.Values) != 2 {
			return dynamicTerm{}, fmt.Errorf("match case must contain a pattern and result")
		}
		pattern, patternOK := entry.Values[0].(List)
		if !patternOK || len(pattern.Values) == 0 {
			return dynamicTerm{}, fmt.Errorf("match pattern must name a constructor")
		}
		constructorName, constructorOK := atomText(pattern.Values[0])
		if !constructorOK {
			return dynamicTerm{}, fmt.Errorf("match constructor must be a symbol")
		}
		var constructor dynamicRecursiveDatatypeConstructor
		found := false
		for _, candidate := range executor.parametricConstructors[constructorName] {
			if candidate.sortCode == target.sort {
				constructor, found = candidate, true
				break
			}
		}
		if !found || len(pattern.Values)-1 != constructor.arity {
			return dynamicTerm{}, fmt.Errorf("ill-sorted match pattern %s", constructorName)
		}
		if _, duplicate := seen[constructor.constructorID]; duplicate {
			return dynamicTerm{}, fmt.Errorf("duplicate match constructor %s", constructorName)
		}
		seen[constructor.constructorID] = struct{}{}
		bound := make([]string, constructor.arity)
		for field := 0; field < constructor.arity; field++ {
			name, nameOK := atomText(pattern.Values[field+1])
			if !nameOK || name == "_" {
				if name == "_" {
					continue
				}
				return dynamicTerm{}, fmt.Errorf("match binder must be a symbol")
			}
			if _, duplicate := executor.localTerms[name]; duplicate {
				return dynamicTerm{}, fmt.Errorf("duplicate or shadowed match binder %s", name)
			}
			selector := constructor
			selector.field = field
			selected, selectErr := selectDynamicMixedDatatypeField(selector, target)
			if selectErr != nil {
				return dynamicTerm{}, selectErr
			}
			executor.localTerms[name], bound[field] = selected, name
		}
		value, valueErr := executor.term(entry.Values[1])
		for _, name := range bound {
			if name != "" {
				delete(executor.localTerms, name)
			}
		}
		if valueErr != nil {
			return dynamicTerm{}, valueErr
		}
		var condition smt.Term[smt.BoolSort]
		if constructor.arity == 0 {
			condition = smt.IsDatatypeConstructor(constructor.datatypeID, constructor.constructors, constructor.constructorID, target.datatype)
		} else {
			condition = smt.IsMixedRecursiveDatatypeConstructor(constructor.mixedWitness, target.datatype)
		}
		branches = append(branches, matchBranch{constructorID: constructor.constructorID, condition: condition, value: value})
	}
	if len(seen) != target.constructorCount {
		return dynamicTerm{}, fmt.Errorf("non-exhaustive datatype match")
	}
	result := branches[len(branches)-1].value
	for index := len(branches) - 2; index >= 0; index-- {
		result, err = dynamicConditional(branches[index].condition, branches[index].value, result)
		if err != nil {
			return dynamicTerm{}, err
		}
	}
	branchValues := make(map[int]dynamicTerm, len(branches))
	for _, branch := range branches {
		branchValues[branch.constructorID] = branch.value
	}
	result.datatypeMatch = &dynamicDatatypeMatch{
		target: target.datatype, datatypeID: target.datatypeID, constructorCount: target.constructorCount, branches: branchValues,
	}
	return result, nil
}

func dynamicConditional(condition smt.Term[smt.BoolSort], then, otherwise dynamicTerm) (dynamicTerm, error) {
	if (then.sort == sortInt || then.sort == sortNumber) && (otherwise.sort == sortInt || otherwise.sort == sortNumber) && then.integer != nil && otherwise.integer != nil {
		return dynamicTerm{sort: sortInt, integer: smt.If[smt.IntSort]{Condition: condition, Then: then.integer, Else: otherwise.integer}}, nil
	}
	if (then.sort == sortReal || then.sort == sortNumber) && (otherwise.sort == sortReal || otherwise.sort == sortNumber) && then.real != nil && otherwise.real != nil {
		return dynamicTerm{sort: sortReal, real: smt.If[smt.RealSort]{Condition: condition, Then: then.real, Else: otherwise.real}}, nil
	}
	if then.sort != otherwise.sort || then.bitWidth != otherwise.bitWidth || then.datatypeID != otherwise.datatypeID || then.constructorCount != otherwise.constructorCount {
		return dynamicTerm{}, fmt.Errorf("match branches must have one result sort")
	}
	if then.datatype != nil && otherwise.datatype != nil {
		return dynamicTerm{
			sort:             then.sort,
			datatype:         smt.If[smt.DatatypeSort]{Condition: condition, Then: then.datatype, Else: otherwise.datatype},
			datatypeID:       then.datatypeID,
			constructorCount: then.constructorCount,
		}, nil
	}
	switch then.sort {
	case sortBool:
		return dynamicTerm{sort: sortBool, boolean: smt.If[smt.BoolSort]{Condition: condition, Then: then.boolean, Else: otherwise.boolean}}, nil
	case sortReal:
		return dynamicTerm{sort: sortReal, real: smt.If[smt.RealSort]{Condition: condition, Then: then.real, Else: otherwise.real}}, nil
	case sortBitVector:
		return dynamicTerm{sort: sortBitVector, bitWidth: then.bitWidth, bitVector: smt.If[smt.BitVecSort]{Condition: condition, Then: then.bitVector, Else: otherwise.bitVector}}, nil
	default:
		return dynamicTerm{}, fmt.Errorf("unsupported datatype match result sort")
	}
}

func indexedDatatypeRecognizerOperator(expression SExpr) (string, bool) {
	indexed, ok := expression.(List)
	if !ok || len(indexed.Values) != 3 {
		return "", false
	}
	marker, markerOK := atomText(indexed.Values[0])
	recognizer, recognizerOK := atomText(indexed.Values[1])
	constructor, constructorOK := atomText(indexed.Values[2])
	return constructor, markerOK && recognizerOK && constructorOK && marker == "_" && recognizer == "is"
}

func indexedDatatypeUpdateOperator(expression SExpr) (string, bool) {
	indexed, ok := expression.(List)
	if !ok || len(indexed.Values) != 3 {
		return "", false
	}
	marker, markerOK := atomText(indexed.Values[0])
	update, updateOK := atomText(indexed.Values[1])
	selector, selectorOK := atomText(indexed.Values[2])
	return selector, markerOK && updateOK && selectorOK && marker == "_" && update == "update-field"
}

func compactDatatypeSelectors(values []string) smt.NaryDatatypeSelectors {
	var result smt.NaryDatatypeSelectors
	for _, value := range values {
		result.Append(value)
	}
	return result
}

func parseDatatypeFieldSort(expression SExpr, enclosing string, references map[string]dynamicDatatype) (datatypeFieldSort, bool) {
	if name, ok := atomText(expression); ok {
		switch name {
		case enclosing:
			return datatypeFieldSort{sort: sortDatatypeSelf}, true
		case "Bool":
			return datatypeFieldSort{sort: sortBool}, true
		case "Int":
			return datatypeFieldSort{sort: sortInt}, true
		case "Real":
			return datatypeFieldSort{sort: sortReal}, true
		}
		if target, found := references[name]; found {
			return datatypeFieldSort{sort: target.sortCode, datatypeID: target.id, constructors: target.constructorCount}, true
		}
	}
	if width, ok := bitVectorSortWidth(expression); ok {
		return datatypeFieldSort{sort: sortBitVector, width: width}, true
	}
	return datatypeFieldSort{}, false
}

func allDatatypeFieldsSelf(fields []datatypeFieldSort, _ int) bool {
	for _, field := range fields {
		if field.sort != sortDatatypeSelf {
			return false
		}
	}
	return true
}

func declareDynamicMixedDatatypeConstructor(datatype dynamicDatatype, constructorID int, constructor datatypeConstructorDeclaration) smt.MixedRecursiveDatatypeConstructor {
	var signature smt.MixedDatatypeSignature = smt.EmptyMixedDatatypeSignature{}
	for field := len(constructor.fieldSorts) - 1; field >= 0; field-- {
		sort, name := constructor.fieldSorts[field], constructor.selectorNames[field]
		switch sort.sort {
		case sortBool:
			signature = smt.BoolDatatypeField(name, signature)
		case sortInt:
			signature = smt.IntDatatypeField(name, signature)
		case sortReal:
			signature = smt.RealDatatypeField(name, signature)
		case sortBitVector:
			signature = smt.BitVecDatatypeField(sort.width, name, signature)
		case sortDatatypeSelf:
			signature = smt.SelfDatatypeField(name, signature)
		default:
			signature = smt.DatatypeReferenceField(sort.datatypeID, sort.constructors, name, signature)
		}
	}
	return smt.DeclareMixedRecursiveDatatypeConstructor(datatype.id, datatype.constructorCount, constructorID, constructor.name, signature)
}

func datatypeFieldAccepts(fields []datatypeFieldSort, field, datatypeSort int, term dynamicTerm) bool {
	if len(fields) == 0 {
		return term.sort == datatypeSort
	}
	expected := fields[field]
	switch expected.sort {
	case sortDatatypeSelf:
		return term.sort == datatypeSort
	case sortInt:
		return term.sort == sortInt || term.sort == sortNumber && term.integer != nil
	case sortReal:
		return term.sort == sortReal || term.sort == sortNumber && term.real != nil
	case sortBitVector:
		return term.sort == sortBitVector && term.bitWidth == expected.width
	default:
		return term.sort == expected.sort
	}
}

func dynamicMixedDatatypeArguments(fields []datatypeFieldSort, terms []dynamicTerm) (smt.MixedDatatypeArguments, bool) {
	var arguments smt.MixedDatatypeArguments = smt.EmptyMixedDatatypeArguments{}
	for field := len(fields) - 1; field >= 0; field-- {
		switch fields[field].sort {
		case sortBool:
			arguments = smt.BoolDatatypeArgument(terms[field].boolean, arguments)
		case sortInt:
			arguments = smt.IntDatatypeArgument(terms[field].integer, arguments)
		case sortReal:
			arguments = smt.RealDatatypeArgument(terms[field].real, arguments)
		case sortBitVector:
			arguments = smt.BitVecDatatypeArgument(fields[field].width, terms[field].bitVector, arguments)
		case sortDatatypeSelf:
			arguments = smt.SelfDatatypeArgument(terms[field].datatype, arguments)
		default:
			if fields[field].datatypeID < 0 || fields[field].constructors <= 0 {
				return nil, false
			}
			arguments = smt.DatatypeReferenceArgument(fields[field].datatypeID, fields[field].constructors, terms[field].datatype, arguments)
		}
	}
	return arguments, true
}

func selectDynamicMixedDatatypeField(selector dynamicRecursiveDatatypeConstructor, target dynamicTerm) (dynamicTerm, error) {
	cursor := smt.MixedDatatypeFields(selector.mixedWitness)
	for field := 0; field < selector.field; field++ {
		cursor = smt.NextMixedDatatypeField(cursor)
	}
	selected := selector.fieldSorts[selector.field]
	switch selected.sort {
	case sortBool:
		return dynamicTerm{sort: sortBool, boolean: smt.SelectMixedBoolDatatypeField(cursor, target.datatype),
			selectorTarget: target.datatype, selectorDatatypeID: target.datatypeID, selectorConstructors: target.constructorCount, selectorField: selector.field}, nil
	case sortInt:
		return dynamicTerm{sort: sortInt, integer: smt.SelectMixedIntDatatypeField(cursor, target.datatype),
			selectorTarget: target.datatype, selectorDatatypeID: target.datatypeID, selectorConstructors: target.constructorCount, selectorField: selector.field}, nil
	case sortReal:
		return dynamicTerm{sort: sortReal, real: smt.SelectMixedRealDatatypeField(cursor, target.datatype),
			selectorTarget: target.datatype, selectorDatatypeID: target.datatypeID, selectorConstructors: target.constructorCount, selectorField: selector.field}, nil
	case sortBitVector:
		return dynamicTerm{sort: sortBitVector, bitWidth: selected.width, bitVector: smt.SelectMixedBitVecDatatypeField(selected.width, cursor, target.datatype),
			selectorTarget: target.datatype, selectorDatatypeID: target.datatypeID, selectorConstructors: target.constructorCount, selectorField: selector.field}, nil
	case sortDatatypeSelf:
		return dynamicTerm{sort: selector.sortCode, datatypeID: target.datatypeID, constructorCount: target.constructorCount, datatype: smt.SelectMixedSelfDatatypeField(cursor, target.datatype)}, nil
	default:
		if selected.datatypeID < 0 || selected.constructors <= 0 {
			return dynamicTerm{}, fmt.Errorf("unsupported datatype selector sort")
		}
		return dynamicTerm{sort: selected.sort, datatypeID: selected.datatypeID, constructorCount: selected.constructors, datatype: smt.SelectMixedDatatypeReferenceField(selected.datatypeID, selected.constructors, cursor, target.datatype)}, nil
	}
}

func updateDynamicMixedDatatypeField(selector dynamicRecursiveDatatypeConstructor, target, replacement dynamicTerm) (dynamicTerm, error) {
	if selector.field < 0 || selector.field >= len(selector.fieldSorts) || !datatypeFieldAccepts(selector.fieldSorts, selector.field, selector.sortCode, replacement) {
		return dynamicTerm{}, fmt.Errorf("ill-sorted datatype update-field")
	}
	cursor := smt.MixedDatatypeFields(selector.mixedWitness)
	for field := 0; field < selector.field; field++ {
		cursor = smt.NextMixedDatatypeField(cursor)
	}
	selected := selector.fieldSorts[selector.field]
	var updated smt.Term[smt.DatatypeSort]
	switch selected.sort {
	case sortBool:
		updated = smt.UpdateMixedBoolDatatypeField(cursor, target.datatype, replacement.boolean)
	case sortInt:
		updated = smt.UpdateMixedIntDatatypeField(cursor, target.datatype, replacement.integer)
	case sortReal:
		updated = smt.UpdateMixedRealDatatypeField(cursor, target.datatype, replacement.real)
	case sortBitVector:
		updated = smt.UpdateMixedBitVecDatatypeField(selected.width, cursor, target.datatype, replacement.bitVector)
	case sortDatatypeSelf:
		updated = smt.UpdateMixedSelfDatatypeField(cursor, target.datatype, replacement.datatype)
	default:
		updated = smt.UpdateMixedDatatypeReferenceField(selected.datatypeID, selected.constructors, cursor, target.datatype, replacement.datatype)
	}
	return dynamicTerm{
		sort: selector.sortCode, datatypeID: selector.datatypeID,
		constructorCount: selector.constructors, datatype: updated,
	}, nil
}

func compactDatatypeTerms(values []dynamicTerm) smt.NaryDatatypeTerms {
	var result smt.NaryDatatypeTerms
	for _, value := range values {
		result.Append(value.datatype)
	}
	return result
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
	stringTerms := func() ([]smt.Term[smt.StringSort], bool) {
		values := make([]smt.Term[smt.StringSort], len(terms))
		for index, term := range terms {
			if term.sort != sortString {
				return nil, false
			}
			values[index] = term.stringValue
		}
		return values, true
	}
	regexTerms := func() ([]smt.Regex[smt.StringSort], bool) {
		values := make([]smt.Regex[smt.StringSort], len(terms))
		for index, term := range terms {
			if term.sort != sortRegexString {
				return nil, false
			}
			values[index] = term.regexString
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
	case "str.to_re":
		if values, ok := stringTerms(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortRegexString, regexString: smt.StringToRegex(values[0])}, nil
		}
	case "str.in_re":
		if len(terms) == 2 && terms[0].sort == sortString && terms[1].sort == sortRegexString {
			return dynamicTerm{sort: sortBool, boolean: smt.StringInRegex(terms[0].stringValue, terms[1].regexString)}, nil
		}
	case "re.range":
		if values, ok := stringTerms(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortRegexString, regexString: smt.StringRangeRegex(values[0], values[1])}, nil
		}
	case "re.++", "re.union", "re.inter":
		if values, ok := regexTerms(); ok && len(values) > 0 {
			result := values[0]
			for _, value := range values[1:] {
				switch operator {
				case "re.++":
					result = smt.ConcatRegex(result, value)
				case "re.union":
					result = smt.UnionRegex(result, value)
				case "re.inter":
					result = smt.IntersectRegex(result, value)
				}
			}
			return dynamicTerm{sort: sortRegexString, regexString: result}, nil
		}
	case "re.diff":
		if values, ok := regexTerms(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortRegexString, regexString: smt.DifferenceRegex(values[0], values[1])}, nil
		}
	case "re.comp":
		if values, ok := regexTerms(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortRegexString, regexString: smt.ComplementRegex(values[0])}, nil
		}
	case "re.*":
		if values, ok := regexTerms(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortRegexString, regexString: smt.StarRegex(values[0])}, nil
		}
	case "re.+":
		if values, ok := regexTerms(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortRegexString, regexString: smt.PlusRegex(values[0])}, nil
		}
	case "re.opt":
		if values, ok := regexTerms(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortRegexString, regexString: smt.OptionalRegex(values[0])}, nil
		}
	case "str.++":
		if values, ok := stringTerms(); ok {
			return dynamicTerm{sort: sortString, stringValue: smt.StringConcat(values...)}, nil
		}
	case "str.len":
		if values, ok := stringTerms(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortInt, integer: smt.StringLength(values[0])}, nil
		}
	case "str.<", "str.<=":
		if values, ok := stringTerms(); ok && len(values) >= 2 {
			comparisons := make([]smt.Term[smt.BoolSort], len(values)-1)
			for index := 1; index < len(values); index++ {
				if operator == "str.<" {
					comparisons[index-1] = smt.StringLess(values[index-1], values[index])
				} else {
					comparisons[index-1] = smt.StringLessEqual(values[index-1], values[index])
				}
			}
			if len(comparisons) == 1 {
				return dynamicTerm{sort: sortBool, boolean: comparisons[0]}, nil
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: comparisons}}, nil
		}
	case "str.contains":
		if values, ok := stringTerms(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortBool, boolean: smt.StringContains(values[0], values[1])}, nil
		}
	case "str.prefixof":
		if values, ok := stringTerms(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortBool, boolean: smt.StringHasPrefix(values[1], values[0])}, nil
		}
	case "str.suffixof":
		if values, ok := stringTerms(); ok && len(values) == 2 {
			return dynamicTerm{sort: sortBool, boolean: smt.StringHasSuffix(values[1], values[0])}, nil
		}
	case "str.at":
		if len(terms) == 2 && terms[0].sort == sortString && (terms[1].sort == sortInt || terms[1].sort == sortNumber && terms[1].integer != nil) {
			return dynamicTerm{sort: sortString, stringValue: smt.StringAt(terms[0].stringValue, terms[1].integer)}, nil
		}
	case "str.substr":
		if len(terms) == 3 && terms[0].sort == sortString &&
			(terms[1].sort == sortInt || terms[1].sort == sortNumber && terms[1].integer != nil) &&
			(terms[2].sort == sortInt || terms[2].sort == sortNumber && terms[2].integer != nil) {
			return dynamicTerm{sort: sortString, stringValue: smt.StringSubstring(terms[0].stringValue, terms[1].integer, terms[2].integer)}, nil
		}
	case "str.indexof":
		if len(terms) == 3 && terms[0].sort == sortString && terms[1].sort == sortString &&
			(terms[2].sort == sortInt || terms[2].sort == sortNumber && terms[2].integer != nil) {
			return dynamicTerm{sort: sortInt, integer: smt.StringIndexOf(terms[0].stringValue, terms[1].stringValue, terms[2].integer)}, nil
		}
	case "str.replace":
		if values, ok := stringTerms(); ok && len(values) == 3 {
			return dynamicTerm{sort: sortString, stringValue: smt.StringReplace(values[0], values[1], values[2])}, nil
		}
	case "str.replace_all":
		if values, ok := stringTerms(); ok && len(values) == 3 {
			return dynamicTerm{sort: sortString, stringValue: smt.StringReplaceAll(values[0], values[1], values[2])}, nil
		}
	case "str.replace_re":
		if len(terms) == 3 && terms[0].sort == sortString &&
			terms[1].sort == sortRegexString && terms[2].sort == sortString {
			return dynamicTerm{
				sort: sortString,
				stringValue: smt.StringReplaceRegex(
					terms[0].stringValue, terms[1].regexString, terms[2].stringValue,
				),
			}, nil
		}
	case "str.replace_re_all":
		if len(terms) == 3 && terms[0].sort == sortString &&
			terms[1].sort == sortRegexString && terms[2].sort == sortString {
			return dynamicTerm{
				sort: sortString,
				stringValue: smt.StringReplaceRegexAll(
					terms[0].stringValue, terms[1].regexString, terms[2].stringValue,
				),
			}, nil
		}
	case "str.to_int":
		if values, ok := stringTerms(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortInt, integer: smt.StringToInt(values[0])}, nil
		}
	case "str.from_int":
		if values, ok := integers(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortString, stringValue: smt.IntToString(values[0])}, nil
		}
	case "str.to_code":
		if values, ok := stringTerms(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortInt, integer: smt.StringToCode(values[0])}, nil
		}
	case "str.from_code":
		if values, ok := integers(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortString, stringValue: smt.StringFromCode(values[0])}, nil
		}
	case "str.is_digit":
		if values, ok := stringTerms(); ok && len(values) == 1 {
			return dynamicTerm{sort: sortBool, boolean: smt.StringIsDigit(values[0])}, nil
		}
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
		if values, ok := stringTerms(); ok && len(values) >= 2 {
			disequalities := make([]smt.Term[smt.BoolSort], 0, len(values)*(len(values)-1)/2)
			for left := 0; left < len(values); left++ {
				for right := left + 1; right < len(values); right++ {
					disequalities = append(disequalities, smt.Not{Value: smt.Equal{Left: values[left], Right: values[right]}})
				}
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: disequalities}}, nil
		}
		if len(terms) >= 2 && terms[0].datatype != nil {
			disequalities := make([]smt.Term[smt.BoolSort], 0, len(terms)*(len(terms)-1)/2)
			for left := 0; left < len(terms); left++ {
				for right := left + 1; right < len(terms); right++ {
					if terms[right].sort != terms[left].sort || terms[right].datatypeID != terms[left].datatypeID || terms[right].constructorCount != terms[left].constructorCount {
						return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
					}
					disequalities = append(disequalities, smt.Not{Value: smt.Equal{Left: terms[left].datatype, Right: terms[right].datatype}})
				}
			}
			if len(disequalities) == 1 {
				return dynamicTerm{sort: sortBool, boolean: disequalities[0]}, nil
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: disequalities}}, nil
		}
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
		if values, ok := stringTerms(); ok && len(values) >= 2 {
			equalities := make([]smt.Term[smt.BoolSort], len(values)-1)
			for index := 1; index < len(values); index++ {
				equalities[index-1] = smt.Equal{Left: values[index-1], Right: values[index]}
			}
			if len(equalities) == 1 {
				return dynamicTerm{sort: sortBool, boolean: equalities[0]}, nil
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: equalities}}, nil
		}
		if len(terms) >= 2 && terms[0].datatype != nil {
			equalities := make([]smt.Term[smt.BoolSort], len(terms)-1)
			for index := 1; index < len(terms); index++ {
				if terms[index].sort != terms[0].sort || terms[index].datatypeID != terms[0].datatypeID || terms[index].constructorCount != terms[0].constructorCount {
					return dynamicTerm{}, fmt.Errorf("ill-sorted application %s", operator)
				}
				equalities[index-1] = smt.Equal{Left: terms[index-1].datatype, Right: terms[index].datatype}
			}
			if len(equalities) == 1 {
				return dynamicTerm{sort: sortBool, boolean: equalities[0]}, nil
			}
			return dynamicTerm{sort: sortBool, boolean: smt.And{Values: equalities}}, nil
		}
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
			if divisor, exact := smt.ExactIntegerConstant(values[1]); exact && smt.CompareIntegerValue(divisor, smt.IntegerValue{}) != 0 {
				return dynamicTerm{sort: sortInt, integer: smt.DivInteger(values[0], divisor)}, nil
			}
		}
	case "mod":
		if values, ok := integers(); ok && len(values) == 2 {
			if divisor, exact := smt.ExactIntegerConstant(values[1]); exact && smt.CompareIntegerValue(divisor, smt.IntegerValue{}) != 0 {
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

func buildIndexedRegexApplication(operator string, parameters []int, terms []dynamicTerm) (dynamicTerm, error) {
	if len(terms) != 1 || terms[0].sort != sortRegexString {
		return dynamicTerm{}, fmt.Errorf("ill-sorted indexed application %s", operator)
	}
	minimum, maximum := 0, -1
	switch operator {
	case "re.^":
		if len(parameters) == 1 {
			minimum, maximum = parameters[0], parameters[0]
		}
	case "re.loop":
		if len(parameters) == 1 {
			minimum, maximum = parameters[0], parameters[0]
		} else if len(parameters) == 2 && parameters[0] <= parameters[1] {
			minimum, maximum = parameters[0], parameters[1]
		}
	}
	if maximum < 0 {
		return dynamicTerm{}, fmt.Errorf("unsupported indexed regex application %s", operator)
	}
	return dynamicTerm{
		sort: sortRegexString, regexString: smt.LoopRegex(minimum, maximum, terms[0].regexString),
	}, nil
}

func isStringRegexSort(expression SExpr) bool {
	list, ok := expression.(List)
	if !ok || len(list.Values) != 2 {
		return false
	}
	name, nameOK := atomText(list.Values[0])
	element, elementOK := atomText(list.Values[1])
	return nameOK && elementOK && name == "RegEx" && element == "String"
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
