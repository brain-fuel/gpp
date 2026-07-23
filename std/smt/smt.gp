// Package smt provides the essential sorted-term and incremental-solver core
// shared by native Go+ theorem provers. It is intentionally independent of
// any one solver's compatibility API.
package smt

import "goforge.dev/goplus/std/vec"

type BoolSort struct{}
type IntSort struct{}
type RealSort struct{}
// DatatypeSort retains both the declaration identity and finite constructor
// cardinality. Go+ therefore rejects terms from distinct datatype
// declarations even when they happen to have the same number of constructors.
//goplus:derive off
type DatatypeSort[d nat, n nat] enum {
	datatypeSort() DatatypeSort[d, n]
}
// RecursiveDatatypeConstructor is a declaration witness for one unary
// constructor whose field recursively has the enclosing datatype sort.
//goplus:derive off
type RecursiveDatatypeConstructor[d nat, n nat, c nat] enum {
	recursiveDatatypeConstructorValue(DatatypeID int, ConstructorCount int, ConstructorID int, Name string, SelectorName string) RecursiveDatatypeConstructor[d, n, c]
}
// BinaryRecursiveDatatypeConstructor witnesses a branching constructor whose
// two fields both have the enclosing datatype sort.
//goplus:derive off
type BinaryRecursiveDatatypeConstructor[d nat, n nat, c nat] enum {
	binaryRecursiveDatatypeConstructorValue(DatatypeID int, ConstructorCount int, ConstructorID int, Name string, FirstSelectorName string, SecondSelectorName string) BinaryRecursiveDatatypeConstructor[d, n, c]
}
// NaryRecursiveDatatypeConstructor witnesses an arbitrary nonempty vector of
// fields, all recursively carrying the enclosing datatype sort. Its arity is
// a dependent index shared by declaration, application, and selector proof.
//goplus:derive off
//goplus:repr transparent
type NaryRecursiveDatatypeConstructor[d nat, n nat, c nat, a nat] enum {
	naryRecursiveDatatypeConstructorValue(DatatypeID int, ConstructorCount int, ConstructorID int, Arity int, Name string, SelectorNames NaryDatatypeSelectors) NaryRecursiveDatatypeConstructor[d, n, c, a]
}
// DatatypeFieldSort is the first-order universe of field sorts supported by
// the native mixed-datatype kernel. DatatypeFieldList is a recursive index
// domain, so a signature is a genuine type-level heterogeneous list.
type DatatypeFieldSort enum {
	BoolDatatypeFieldSort()
	IntDatatypeFieldSort()
	RealDatatypeFieldSort()
	BitVecDatatypeFieldSort(Width nat)
	SelfDatatypeFieldSort()
}
type DatatypeFieldList enum {
	NoDatatypeFields()
	DatatypeFieldCons(Head DatatypeFieldSort, Tail DatatypeFieldList)
}
//goplus:derive off
type MixedDatatypeSignature[fields DatatypeFieldList] enum {
	EmptyMixedDatatypeSignature() MixedDatatypeSignature[NoDatatypeFields]
	mixedDatatypeSignatureValue(Specs MixedDatatypeFieldSpecs) MixedDatatypeSignature[fields]
}
//goplus:derive off
type MixedDatatypeArguments[d nat, n nat, fields DatatypeFieldList] enum {
	EmptyMixedDatatypeArguments() MixedDatatypeArguments[d, n, NoDatatypeFields]
	mixedDatatypeArgumentsValue(Values MixedDatatypeTermValues) MixedDatatypeArguments[d, n, fields]
}
//goplus:derive off
//goplus:repr transparent
type MixedRecursiveDatatypeConstructor[d nat, n nat, c nat, fields DatatypeFieldList] enum {
	mixedRecursiveDatatypeConstructorValue(DatatypeID int, ConstructorCount int, ConstructorID int, Name string, Specs MixedDatatypeFieldSpecs) MixedRecursiveDatatypeConstructor[d, n, c, fields]
}
// MixedDatatypeCursor is a typed cursor into a constructor signature. Moving
// to the tail changes its list index; selecting the head therefore returns the
// statically correct SMT sort without an untyped field-number API.
//goplus:derive off
//goplus:repr transparent
type MixedDatatypeCursor[d nat, n nat, c nat, fields DatatypeFieldList] enum {
	mixedDatatypeCursorValue(Declaration MixedRecursiveDatatypeConstructor[d, n, c, fields], Offset int) MixedDatatypeCursor[d, n, c, fields]
}
type BinaryDatatypeField enum {
	FirstDatatypeField() BinaryDatatypeField
	SecondDatatypeField() BinaryDatatypeField
}
//goplus:derive off
type ArraySort[I any, E any] enum {
	arraySort() ArraySort[I, E]
}
//goplus:derive off
type BitVecSort[w nat] enum {
	bitVecSort() BitVecSort[w]
}
//goplus:derive off
type UninterpretedSort[s nat] enum {
	uninterpretedSort() UninterpretedSort[s]
}

// UnaryFunction[d,r] retains its uninterpreted domain and range sorts. Go+
// rejects applying it to a term from another domain before Go generation.
//goplus:derive off
type UnaryFunction[d nat, r nat] enum {
	unaryFunctionValue(DomainID int, RangeID int, ID int, Name string) UnaryFunction[d, r]
}

// BinaryFunction[a,b,r] retains both argument sorts and its result sort.
// Go+ rejects swapped or otherwise ill-sorted applications before generation.
//goplus:derive off
type BinaryFunction[a nat, b nat, r nat] enum {
	binaryFunctionValue(FirstID int, SecondID int, RangeID int, ID int, Name string) BinaryFunction[a, b, r]
}

// SortedUnaryFunction[D,R] extends typed EUF to built-in sorts. The type
// indices prevent applying a Real function to an Int or uninterpreted term.
//goplus:derive off
type SortedUnaryFunction[D any, R any] enum {
	sortedUnaryFunctionValue(DomainKind int, RangeKind int, ID int, Name string) SortedUnaryFunction[D, R]
}

// SortedBinaryFunction[A,B,R] extends typed binary EUF to built-in sorts.
// All three sort indices are checked before Go generation.
//goplus:derive off
type SortedBinaryFunction[A any, B any, R any] enum {
	sortedBinaryFunctionValue(FirstKind int, SecondKind int, RangeKind int, ID int, Name string) SortedBinaryFunction[A, B, R]
}

// Term[S] makes ill-sorted formulas unrepresentable in Go+.
type Term[S any] enum {
	Bool(Value bool) Term[BoolSort]
	BoolSymbol(ID int, Name string) Term[BoolSort]
	BooleanVariable(ID int) Term[BoolSort]
	NegatedBooleanVariable(ID int) Term[BoolSort]
	BooleanClause(Literals []int) Term[BoolSort]
	BooleanCNF(Literals []int, ClauseEnds []int) Term[BoolSort]
	Not(Value Term[BoolSort]) Term[BoolSort]
	And(Values []Term[BoolSort]) Term[BoolSort]
	Or(Values []Term[BoolSort]) Term[BoolSort]
	Implies(Left Term[BoolSort], Right Term[BoolSort]) Term[BoolSort]
	Iff(Left Term[BoolSort], Right Term[BoolSort]) Term[BoolSort]
	If(Condition Term[BoolSort], Then Term[S], Else Term[S]) Term[S]
	Equal[X any](Left Term[X], Right Term[X]) Term[BoolSort]
	Integer(Value int64) Term[IntSort]
	integerExact(Value IntegerValue) Term[S]
	IntSymbol(ID int, Name string) Term[IntSort]
	integerVariable(ID int) Term[S]
	Add(Values []Term[IntSort]) Term[IntSort]
	Subtract(Left Term[IntSort], Right Term[IntSort]) Term[IntSort]
	IntegerScale(Coefficient IntegerValue, Value Term[IntSort]) Term[IntSort]
	IntegerDiv(Dividend Term[IntSort], Divisor IntegerValue) Term[IntSort]
	IntegerMod(Dividend Term[IntSort], Divisor IntegerValue) Term[IntSort]
	LessEqual(Left Term[IntSort], Right Term[IntSort]) Term[BoolSort]
	Less(Left Term[IntSort], Right Term[IntSort]) Term[BoolSort]
	Real(Value Rational) Term[RealSort]
	RealSymbol(ID int, Name string) Term[RealSort]
	RealAdd(Values []Term[RealSort]) Term[RealSort]
	RealSubtract(Left Term[RealSort], Right Term[RealSort]) Term[RealSort]
	RealScale(Coefficient Rational, Value Term[RealSort]) Term[RealSort]
	RealLessEqual(Left Term[RealSort], Right Term[RealSort]) Term[BoolSort]
	RealLess(Left Term[RealSort], Right Term[RealSort]) Term[BoolSort]
	uninterpretedValue(SortID int, ID int, Name string) Term[S]
	unaryApplication(Function any, Argument any) Term[S]
	binaryApplication(Function any, First any, Second any) Term[S]
	sortedUnaryApplication(Function any, Argument any, RangeKind int) Term[S]
	sortedBinaryApplication(Function any, First any, Second any, RangeKind int) Term[S]
	bitVector(Value BitVectorValue) Term[S]
	bitVectorSymbol(Width int, ID int, Name string) Term[S]
	bitVectorNot(Value any) Term[S]
	bitVectorAnd(Left any, Right any) Term[S]
	bitVectorOr(Left any, Right any) Term[S]
	bitVectorXor(Left any, Right any) Term[S]
	bitVectorAdd(Left any, Right any) Term[S]
	bitVectorSub(Left any, Right any) Term[S]
	bitVectorMul(Left any, Right any) Term[S]
	bitVectorShiftLeft(Value any, Amount any) Term[S]
	bitVectorLogicalShiftRight(Value any, Amount any) Term[S]
	bitVectorArithmeticShiftRight(Value any, Amount any) Term[S]
	bitVectorUnsignedDiv(Left any, Right any) Term[S]
	bitVectorUnsignedRem(Left any, Right any) Term[S]
	bitVectorSignedDiv(Left any, Right any) Term[S]
	bitVectorSignedRem(Left any, Right any) Term[S]
	bitVectorConcat(First any, Second any, FirstWidth int, SecondWidth int) Term[S]
	bitVectorExtract(Value any, High int, Low int) Term[S]
	bitVectorZeroExtend(Value any, Additional int) Term[S]
	bitVectorSignExtend(Value any, Additional int) Term[S]
	bitVectorRotateLeft(Value any, Amount int) Term[S]
	bitVectorRotateRight(Value any, Amount int) Term[S]
	bitVectorRepeat(Value any, Count int) Term[S]
	bitVectorUnsignedLess(Left any, Right any, OrEqual bool) Term[S]
	bitVectorSignedLess(Left any, Right any, OrEqual bool) Term[S]
	bitVectorUnsignedAddOverflow(Left any, Right any) Term[S]
	bitVectorSignedAddOverflow(Left any, Right any) Term[S]
	bitVectorUnsignedSubOverflow(Left any, Right any) Term[S]
	bitVectorSignedSubOverflow(Left any, Right any) Term[S]
	bitVectorUnsignedMulOverflow(Left any, Right any) Term[S]
	bitVectorSignedMulOverflow(Left any, Right any) Term[S]
	bitVectorSignedDivOverflow(Left any, Right any) Term[S]
	bitVectorNegOverflow(Value any) Term[S]
	bitVectorToInteger(Value any, Signed bool) Term[S]
	integerToBitVector(Value any, Width int) Term[S]
	arraySymbol(ID int, Name string) Term[S]
	constantArray(DefaultValue any) Term[S]
	arraySelect(Array any, Index any) Term[S]
	arrayStore(Array any, Index any, Value any) Term[S]
	arrayReadInteger(ArrayID int, Index IntegerValue) Term[S]
	arrayStoreReadInteger(ArrayID int, StoreIndexID int, ReadIndexID int, Value IntegerValue) Term[S]
	datatypeSymbol(DatatypeID int, ConstructorCount int, ID int, Name string) Term[S]
	datatypeConstructor(DatatypeID int, ConstructorCount int, ConstructorID int, Name string) Term[S]
	datatypeRecognizer(DatatypeID int, ConstructorCount int, ConstructorID int, Value any) Term[BoolSort]
	datatypeRecursiveRecognizer(DatatypeID int, ConstructorCount int, ConstructorID int, Name string, SelectorName string, Value any) Term[BoolSort]
	datatypeRecursiveApplication(DatatypeID int, ConstructorCount int, ConstructorID int, Name string, SelectorName string, Value any) Term[S]
	datatypeRecursiveSelector(DatatypeID int, ConstructorCount int, ConstructorID int, SelectorName string, Value any) Term[S]
	datatypeBinaryRecursiveApplication(DatatypeID int, ConstructorCount int, ConstructorID int, Name string, FirstSelectorName string, SecondSelectorName string, First any, Second any) Term[S]
	datatypeBinaryRecursiveSelector(DatatypeID int, ConstructorCount int, ConstructorID int, Field int, SelectorName string, Value any) Term[S]
	datatypeBinaryRecursiveRecognizer(DatatypeID int, ConstructorCount int, ConstructorID int, Name string, Value any) Term[BoolSort]
	datatypeNaryRecursiveApplication(DatatypeID int, ConstructorCount int, ConstructorID int, Arity int, Name string, SelectorNames NaryDatatypeSelectors, Values NaryDatatypeTerms) Term[S]
	datatypeNaryRecursiveSelector(DatatypeID int, ConstructorCount int, ConstructorID int, Arity int, Field int, SelectorName string, Value any) Term[S]
	datatypeNaryRecursiveRecognizer(DatatypeID int, ConstructorCount int, ConstructorID int, Arity int, Name string, Value any) Term[BoolSort]
	datatypeMixedApplication(DatatypeID int, ConstructorCount int, ConstructorID int, Name string, Specs MixedDatatypeFieldSpecs, Values MixedDatatypeTermValues) Term[S]
	datatypeMixedSelector(DatatypeID int, ConstructorCount int, ConstructorID int, Field int, FieldKind int, Width int, SelectorName string, Value any) Term[S]
	datatypeMixedRecognizer(DatatypeID int, ConstructorCount int, ConstructorID int, Name string, Specs MixedDatatypeFieldSpecs, Value any) Term[BoolSort]
}

type AnyTerm enum {
	SomeBool(Value Term[BoolSort])
	SomeInt(Value Term[IntSort])
	SomeReal(Value Term[RealSort])
}

type UnknownReason enum {
	UnsupportedTheory(Name string)
	ResourceLimit(Limit int)
	Canceled()
}

// Solver[c,d] has assertion fingerprint c and scope depth d. Constructors are
// sealed so generated Go callers cross runtime witness checks.
//goplus:derive off
//goplus:repr transparent
type Solver[c nat, d nat] enum {
	solverValue(ContextID int, Depth int, State *engine) Solver[c, d]
}

// Model[c] and Proof[c] can only be consumed with terms/assertions from the
// checked solver context that produced them.
//goplus:derive off
//goplus:repr transparent
type Model[c nat] enum {
	modelValue(ContextID int, Booleans booleanModel, Integers integerModel, Reals rationalModel, BitVectors bitVectorModel, Arrays *integerArrayModel, BitVectorArrays *bitVectorArrayModel, Datatypes *datatypeModel) Model[c]
}

//goplus:derive off
//goplus:repr transparent
type Proof[c nat] enum {
	proofValue(ContextID int, Assertions int) Proof[c]
}

type CheckResult[c nat] enum {
	Satisfiable(Value Model[c])
	Unsatisfiable(Value Proof[c])
	Unknown(Context Proof[c], Reason UnknownReason)
}

type AssumptionCheckResult[c nat] enum {
	AssumptionsSatisfiable(Value Model[c])
	AssumptionsUnsatisfiable(Value Proof[c], Indices []int)
	AssumptionsUnknown(Context Proof[c], Reason UnknownReason)
}

// Checkpoint packages the pre-push context. Restore requires the exact
// checkpoint rather than accepting an untyped integer depth.
//goplus:derive off
//goplus:repr transparent
type Checkpoint[c nat, d nat] enum {
	checkpointValue(ContextID int, Depth int, State *engine) Checkpoint[c, d]
}

//goplus:derive off
//goplus:repr transparent
type Pushed[c nat, d nat] enum {
	PushResult(Current Solver[c, d+1], Previous Checkpoint[c, d])
}

total func ContextID(context nat, assertion nat) nat {
	return ((context+assertion)*(context+assertion+1)+assertion)+1
}

func New() Solver[0, 0] { return solverValue(0, 0, newEngine()) }

func IntegerTerm(value IntegerValue) Term[IntSort] { return Term[IntSort].integerExact(value) }
func IntegerVariable(id int) Term[IntSort] { return Term[IntSort].integerVariable(id) }
func ScaleInteger(coefficient IntegerValue, value Term[IntSort]) Term[IntSort] {
	return IntegerScale(coefficient, value)
}
func DivInteger(dividend Term[IntSort], divisor IntegerValue) Term[IntSort] {
	return IntegerDiv(dividend, divisor)
}
func ModInteger(dividend Term[IntSort], divisor IntegerValue) Term[IntSort] {
	return IntegerMod(dividend, divisor)
}

// DatatypeConst creates a symbolic value of an algebraic datatype.
// datatype is its declaration identity; constructors is retained in the sort.
func DatatypeConst(datatype nat, constructors nat, id int, name string) Term[DatatypeSort[datatype, constructors]] {
	if constructors == 0 { panic("smt: datatype requires at least one constructor") }
	return Term[DatatypeSort[datatype, constructors]].datatypeSymbol(int(datatype), int(constructors), id, name)
}

// DatatypeConstructor creates one nullary constructor value. The constructor
// ordinal is checked at runtime and the datatype/cardinality remain indexed.
func DatatypeConstructor(datatype nat, constructors nat, constructor nat, name string) Term[DatatypeSort[datatype, constructors]] {
	if constructors == 0 || constructor >= constructors { panic("smt: datatype constructor outside datatype cardinality") }
	return Term[DatatypeSort[datatype, constructors]].datatypeConstructor(int(datatype), int(constructors), int(constructor), name)
}

func IsDatatypeConstructor(datatype nat, constructors nat, constructor nat, value Term[DatatypeSort[datatype, constructors]]) Term[BoolSort] {
	if constructors == 0 || constructor >= constructors { panic("smt: datatype recognizer outside datatype cardinality") }
	return datatypeRecognizer(int(datatype), int(constructors), int(constructor), value)
}

func DeclareRecursiveDatatypeConstructor(datatype nat, constructors nat, constructor nat, name string, selectorName string) RecursiveDatatypeConstructor[datatype, constructors, constructor] {
	if constructors < 2 || constructor >= constructors { panic("smt: recursive constructor requires a possible base constructor inside datatype cardinality") }
	return recursiveDatatypeConstructorValue(int(datatype), int(constructors), int(constructor), name, selectorName)
}

func ApplyRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, declaration RecursiveDatatypeConstructor[datatype, constructors, constructor], value Term[DatatypeSort[datatype, constructors]]) Term[DatatypeSort[datatype, constructors]] {
	match declaration { case recursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, name, selectorName):
		return Term[DatatypeSort[datatype, constructors]].datatypeRecursiveApplication(datatypeID, constructorCount, constructorID, name, selectorName, value)
	}
}

func SelectRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, declaration RecursiveDatatypeConstructor[datatype, constructors, constructor], value Term[DatatypeSort[datatype, constructors]]) Term[DatatypeSort[datatype, constructors]] {
	match declaration { case recursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, _, selectorName):
		return Term[DatatypeSort[datatype, constructors]].datatypeRecursiveSelector(datatypeID, constructorCount, constructorID, selectorName, value)
	}
}

func IsRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, declaration RecursiveDatatypeConstructor[datatype, constructors, constructor], value Term[DatatypeSort[datatype, constructors]]) Term[BoolSort] {
	match declaration { case recursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, name, selectorName):
		return datatypeRecursiveRecognizer(datatypeID, constructorCount, constructorID, name, selectorName, value)
	}
}

func DeclareBinaryRecursiveDatatypeConstructor(datatype nat, constructors nat, constructor nat, name string, firstSelectorName string, secondSelectorName string) BinaryRecursiveDatatypeConstructor[datatype, constructors, constructor] {
	if constructors < 2 || constructor >= constructors { panic("smt: binary recursive constructor requires a possible base constructor inside datatype cardinality") }
	if firstSelectorName == secondSelectorName { panic("smt: binary recursive constructor selectors must be distinct") }
	return binaryRecursiveDatatypeConstructorValue(int(datatype), int(constructors), int(constructor), name, firstSelectorName, secondSelectorName)
}

func ApplyBinaryRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, declaration BinaryRecursiveDatatypeConstructor[datatype, constructors, constructor], first Term[DatatypeSort[datatype, constructors]], second Term[DatatypeSort[datatype, constructors]]) Term[DatatypeSort[datatype, constructors]] {
	match declaration { case binaryRecursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, name, firstSelectorName, secondSelectorName):
		return Term[DatatypeSort[datatype, constructors]].datatypeBinaryRecursiveApplication(datatypeID, constructorCount, constructorID, name, firstSelectorName, secondSelectorName, first, second)
	}
}

func SelectBinaryRecursiveDatatypeConstructor(field BinaryDatatypeField, 0 datatype nat, 0 constructors nat, 0 constructor nat, declaration BinaryRecursiveDatatypeConstructor[datatype, constructors, constructor], value Term[DatatypeSort[datatype, constructors]]) Term[DatatypeSort[datatype, constructors]] {
	match declaration { case binaryRecursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, _, firstSelectorName, secondSelectorName):
		match field {
		case FirstDatatypeField(): return Term[DatatypeSort[datatype, constructors]].datatypeBinaryRecursiveSelector(datatypeID, constructorCount, constructorID, 0, firstSelectorName, value)
		case SecondDatatypeField(): return Term[DatatypeSort[datatype, constructors]].datatypeBinaryRecursiveSelector(datatypeID, constructorCount, constructorID, 1, secondSelectorName, value)
		}
	}
}

func IsBinaryRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, declaration BinaryRecursiveDatatypeConstructor[datatype, constructors, constructor], value Term[DatatypeSort[datatype, constructors]]) Term[BoolSort] {
	match declaration { case binaryRecursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, name, _, _):
		return datatypeBinaryRecursiveRecognizer(datatypeID, constructorCount, constructorID, name, value)
	}
}

func DeclareNaryRecursiveDatatypeConstructor(datatype nat, constructors nat, constructor nat, arity nat, name string, selectorNames vec.Vec[string, arity]) NaryRecursiveDatatypeConstructor[datatype, constructors, constructor, arity] {
	if constructors < 2 || constructor >= constructors { panic("smt: n-ary recursive constructor requires a possible base constructor inside datatype cardinality") }
	if arity == 0 { panic("smt: n-ary recursive constructor requires at least one field") }
	names := compactNaryDatatypeSelectors(selectorNames)
	for left := 0; left < names.Len(); left++ { for right := left+1; right < names.Len(); right++ { if names.At(left) == names.At(right) { panic("smt: n-ary recursive constructor selectors must be distinct") } } }
	return naryRecursiveDatatypeConstructorValue(int(datatype), int(constructors), int(constructor), int(arity), name, names)
}

func ApplyNaryRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 arity nat, declaration NaryRecursiveDatatypeConstructor[datatype, constructors, constructor, arity], values vec.Vec[Term[DatatypeSort[datatype, constructors]], arity]) Term[DatatypeSort[datatype, constructors]] {
	match declaration { case naryRecursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, runtimeArity, name, selectorNames):
		return Term[DatatypeSort[datatype, constructors]].datatypeNaryRecursiveApplication(datatypeID, constructorCount, constructorID, runtimeArity, name, selectorNames, compactNaryDatatypeTerms(values))
	}
}

func SelectNaryRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 arity nat, field vec.Fin[arity], declaration NaryRecursiveDatatypeConstructor[datatype, constructors, constructor, arity], value Term[DatatypeSort[datatype, constructors]]) Term[DatatypeSort[datatype, constructors]] {
	match declaration { case naryRecursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, runtimeArity, _, selectorNames):
		fieldIndex := datatypeFieldIndex(field)
		return Term[DatatypeSort[datatype, constructors]].datatypeNaryRecursiveSelector(datatypeID, constructorCount, constructorID, runtimeArity, fieldIndex, selectorNames.At(fieldIndex), value)
	}
}

func IsNaryRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 arity nat, declaration NaryRecursiveDatatypeConstructor[datatype, constructors, constructor, arity], value Term[DatatypeSort[datatype, constructors]]) Term[BoolSort] {
	match declaration { case naryRecursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, runtimeArity, name, _):
		return datatypeNaryRecursiveRecognizer(datatypeID, constructorCount, constructorID, runtimeArity, name, value)
	}
}

func datatypeFieldIndex(0 n nat, field vec.Fin[n]) int {
	match field {
	case vec.Zero(): return 0
	case vec.Succ(previous): return 1 + datatypeFieldIndex(previous)
	}
}

func BoolDatatypeField(name string, 0 tail DatatypeFieldList, rest MixedDatatypeSignature[tail]) MixedDatatypeSignature[DatatypeFieldCons(BoolDatatypeFieldSort, tail)] {
	match rest {
	case EmptyMixedDatatypeSignature(): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldBool, 0, name, MixedDatatypeFieldSpecs{}))
	case mixedDatatypeSignatureValue(specs): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldBool, 0, name, specs))
	}
}

func IntDatatypeField(name string, 0 tail DatatypeFieldList, rest MixedDatatypeSignature[tail]) MixedDatatypeSignature[DatatypeFieldCons(IntDatatypeFieldSort, tail)] {
	match rest {
	case EmptyMixedDatatypeSignature(): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldInt, 0, name, MixedDatatypeFieldSpecs{}))
	case mixedDatatypeSignatureValue(specs): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldInt, 0, name, specs))
	}
}

func RealDatatypeField(name string, 0 tail DatatypeFieldList, rest MixedDatatypeSignature[tail]) MixedDatatypeSignature[DatatypeFieldCons(RealDatatypeFieldSort, tail)] {
	match rest {
	case EmptyMixedDatatypeSignature(): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldReal, 0, name, MixedDatatypeFieldSpecs{}))
	case mixedDatatypeSignatureValue(specs): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldReal, 0, name, specs))
	}
}

func BitVecDatatypeField(width nat, name string, 0 tail DatatypeFieldList, rest MixedDatatypeSignature[tail]) MixedDatatypeSignature[DatatypeFieldCons(BitVecDatatypeFieldSort(width), tail)] {
	if width <= 0 { panic("smt: mixed datatype bit-vector field width must be positive") }
	match rest {
	case EmptyMixedDatatypeSignature(): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldBitVec, int(width), name, MixedDatatypeFieldSpecs{}))
	case mixedDatatypeSignatureValue(specs): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldBitVec, int(width), name, specs))
	}
}

func SelfDatatypeField(name string, 0 tail DatatypeFieldList, rest MixedDatatypeSignature[tail]) MixedDatatypeSignature[DatatypeFieldCons(SelfDatatypeFieldSort, tail)] {
	match rest {
	case EmptyMixedDatatypeSignature(): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldSelf, 0, name, MixedDatatypeFieldSpecs{}))
	case mixedDatatypeSignatureValue(specs): return mixedDatatypeSignatureValue(prependMixedDatatypeFieldSpec(mixedDatatypeFieldSelf, 0, name, specs))
	}
}

func BoolDatatypeArgument(0 datatype nat, 0 constructors nat, 0 tail DatatypeFieldList, value Term[BoolSort], rest MixedDatatypeArguments[datatype, constructors, tail]) MixedDatatypeArguments[datatype, constructors, DatatypeFieldCons(BoolDatatypeFieldSort, tail)] {
	match rest { case EmptyMixedDatatypeArguments(): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldBool, 0, value, MixedDatatypeTermValues{})); case mixedDatatypeArgumentsValue(values): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldBool, 0, value, values)) }
}
func IntDatatypeArgument(0 datatype nat, 0 constructors nat, 0 tail DatatypeFieldList, value Term[IntSort], rest MixedDatatypeArguments[datatype, constructors, tail]) MixedDatatypeArguments[datatype, constructors, DatatypeFieldCons(IntDatatypeFieldSort, tail)] {
	match rest { case EmptyMixedDatatypeArguments(): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldInt, 0, value, MixedDatatypeTermValues{})); case mixedDatatypeArgumentsValue(values): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldInt, 0, value, values)) }
}
func RealDatatypeArgument(0 datatype nat, 0 constructors nat, 0 tail DatatypeFieldList, value Term[RealSort], rest MixedDatatypeArguments[datatype, constructors, tail]) MixedDatatypeArguments[datatype, constructors, DatatypeFieldCons(RealDatatypeFieldSort, tail)] {
	match rest { case EmptyMixedDatatypeArguments(): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldReal, 0, value, MixedDatatypeTermValues{})); case mixedDatatypeArgumentsValue(values): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldReal, 0, value, values)) }
}
func BitVecDatatypeArgument(width nat, 0 datatype nat, 0 constructors nat, 0 tail DatatypeFieldList, value Term[BitVecSort[width]], rest MixedDatatypeArguments[datatype, constructors, tail]) MixedDatatypeArguments[datatype, constructors, DatatypeFieldCons(BitVecDatatypeFieldSort(width), tail)] {
	match rest { case EmptyMixedDatatypeArguments(): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldBitVec, int(width), value, MixedDatatypeTermValues{})); case mixedDatatypeArgumentsValue(values): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldBitVec, int(width), value, values)) }
}
func SelfDatatypeArgument(0 datatype nat, 0 constructors nat, 0 tail DatatypeFieldList, value Term[DatatypeSort[datatype, constructors]], rest MixedDatatypeArguments[datatype, constructors, tail]) MixedDatatypeArguments[datatype, constructors, DatatypeFieldCons(SelfDatatypeFieldSort, tail)] {
	match rest { case EmptyMixedDatatypeArguments(): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldSelf, 0, value, MixedDatatypeTermValues{})); case mixedDatatypeArgumentsValue(values): return mixedDatatypeArgumentsValue(prependMixedDatatypeTerm(mixedDatatypeFieldSelf, 0, value, values)) }
}

func DeclareMixedRecursiveDatatypeConstructor(datatype nat, constructors nat, constructor nat, 0 fields DatatypeFieldList, name string, signature MixedDatatypeSignature[fields]) MixedRecursiveDatatypeConstructor[datatype, constructors, constructor, fields] {
	if constructors < 1 || constructor >= constructors { panic("smt: mixed datatype constructor is outside its declaration") }
	match signature {
	case EmptyMixedDatatypeSignature(): panic("smt: mixed recursive constructor requires at least one field")
	case mixedDatatypeSignatureValue(specs): validateMixedDatatypeFieldSpecs(specs); return mixedRecursiveDatatypeConstructorValue(int(datatype), int(constructors), int(constructor), name, specs)
	}
}

func ApplyMixedRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 fields DatatypeFieldList, declaration MixedRecursiveDatatypeConstructor[datatype, constructors, constructor, fields], arguments MixedDatatypeArguments[datatype, constructors, fields]) Term[DatatypeSort[datatype, constructors]] {
	match declaration { case mixedRecursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, name, specs): match arguments {
	case EmptyMixedDatatypeArguments(): panic("smt: mixed recursive constructor requires at least one field")
	case mixedDatatypeArgumentsValue(values): validateMixedDatatypeArguments(specs, values); return Term[DatatypeSort[datatype, constructors]].datatypeMixedApplication(datatypeID, constructorCount, constructorID, name, specs, values)
	} }
}

func MixedDatatypeFields(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 fields DatatypeFieldList, declaration MixedRecursiveDatatypeConstructor[datatype, constructors, constructor, fields]) MixedDatatypeCursor[datatype, constructors, constructor, fields] { return mixedDatatypeCursorValue(declaration, 0) }
func NextMixedDatatypeField(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 head DatatypeFieldSort, 0 tail DatatypeFieldList, cursor MixedDatatypeCursor[datatype, constructors, constructor, DatatypeFieldCons(head, tail)]) MixedDatatypeCursor[datatype, constructors, constructor, tail] { match cursor { case mixedDatatypeCursorValue(declaration, offset): return mixedDatatypeCursorValue(declaration, offset+1) } }

func SelectMixedBoolDatatypeField(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail DatatypeFieldList, cursor MixedDatatypeCursor[datatype, constructors, constructor, DatatypeFieldCons(BoolDatatypeFieldSort, tail)], value Term[DatatypeSort[datatype, constructors]]) Term[BoolSort] { return selectMixedDatatypeField[BoolSort](mixedDatatypeFieldBool, 0, cursor, value) }
func SelectMixedIntDatatypeField(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail DatatypeFieldList, cursor MixedDatatypeCursor[datatype, constructors, constructor, DatatypeFieldCons(IntDatatypeFieldSort, tail)], value Term[DatatypeSort[datatype, constructors]]) Term[IntSort] { return selectMixedDatatypeField[IntSort](mixedDatatypeFieldInt, 0, cursor, value) }
func SelectMixedRealDatatypeField(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail DatatypeFieldList, cursor MixedDatatypeCursor[datatype, constructors, constructor, DatatypeFieldCons(RealDatatypeFieldSort, tail)], value Term[DatatypeSort[datatype, constructors]]) Term[RealSort] { return selectMixedDatatypeField[RealSort](mixedDatatypeFieldReal, 0, cursor, value) }
func SelectMixedBitVecDatatypeField(width nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail DatatypeFieldList, cursor MixedDatatypeCursor[datatype, constructors, constructor, DatatypeFieldCons(BitVecDatatypeFieldSort(width), tail)], value Term[DatatypeSort[datatype, constructors]]) Term[BitVecSort[width]] { return selectMixedDatatypeField[BitVecSort[width]](mixedDatatypeFieldBitVec, int(width), cursor, value) }
func SelectMixedSelfDatatypeField(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail DatatypeFieldList, cursor MixedDatatypeCursor[datatype, constructors, constructor, DatatypeFieldCons(SelfDatatypeFieldSort, tail)], value Term[DatatypeSort[datatype, constructors]]) Term[DatatypeSort[datatype, constructors]] { return selectMixedDatatypeField[DatatypeSort[datatype, constructors]](mixedDatatypeFieldSelf, 0, cursor, value) }

func selectMixedDatatypeField[S any](kind int, width int, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 fields DatatypeFieldList, cursor MixedDatatypeCursor[datatype, constructors, constructor, fields], value Term[DatatypeSort[datatype, constructors]]) Term[S] { match cursor { case mixedDatatypeCursorValue(declaration, offset): match declaration { case mixedRecursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, _, specs): spec := specs.At(offset); if spec.Kind != kind || spec.Width != width { panic("smt: erased mixed datatype cursor sort mismatch") }; return Term[S].datatypeMixedSelector(datatypeID, constructorCount, constructorID, offset, kind, width, spec.Name, value) } } }
func IsMixedRecursiveDatatypeConstructor(0 datatype nat, 0 constructors nat, 0 constructor nat, 0 fields DatatypeFieldList, declaration MixedRecursiveDatatypeConstructor[datatype, constructors, constructor, fields], value Term[DatatypeSort[datatype, constructors]]) Term[BoolSort] { match declaration { case mixedRecursiveDatatypeConstructorValue(datatypeID, constructorCount, constructorID, name, specs): return datatypeMixedRecognizer(datatypeID, constructorCount, constructorID, name, specs, value) } }

func IntegerVariableID(term Term[IntSort]) (int, bool) {
	match term {
	case IntSymbol(id, _):
		return id, true
	case integerVariable(id):
		return id, true
	case _:
		return 0, false
	}
}

func ArrayConst[I any, E any](id int, name string) Term[ArraySort[I, E]] {
	return Term[ArraySort[I, E]].arraySymbol(id, name)
}

func ConstArray[I any, E any](value Term[E]) Term[ArraySort[I, E]] {
	return Term[ArraySort[I, E]].constantArray(value)
}

func Select[I any, E any](array Term[ArraySort[I, E]], index Term[I]) Term[E] {
	return Term[E].arraySelect(array, index)
}

func Store[I any, E any](array Term[ArraySort[I, E]], index Term[I], value Term[E]) Term[ArraySort[I, E]] {
	return Term[ArraySort[I, E]].arrayStore(array, index, value)
}

func IntegerArrayRead(arrayID int, index IntegerValue) Term[IntSort] {
	return Term[IntSort].arrayReadInteger(arrayID, index)
}

func SymbolicIntegerArrayStoreRead(arrayID int, storeIndexID int, readIndexID int, value IntegerValue) Term[IntSort] {
	return Term[IntSort].arrayStoreReadInteger(arrayID, storeIndexID, readIndexID, value)
}

func UninterpretedConstant(sort nat, id int, name string) Term[UninterpretedSort[sort]] {
	if sort < 0 { panic("smt: negative uninterpreted sort identity") }
	return Term[UninterpretedSort[sort]].uninterpretedValue(sort, id, name)
}

func DeclareUnaryFunction(domain nat, codomain nat, id int, name string) UnaryFunction[domain, codomain] {
	if domain < 0 || codomain < 0 { panic("smt: negative uninterpreted function sort identity") }
	return UnaryFunction[domain, codomain].unaryFunctionValue(int(domain), int(codomain), id, name)
}

func ApplyUnary(0 domain nat, 0 codomain nat, function UnaryFunction[domain, codomain], argument Term[UninterpretedSort[domain]]) Term[UninterpretedSort[codomain]] {
	return Term[UninterpretedSort[codomain]].unaryApplication(function, argument)
}

func DeclareBinaryFunction(first nat, second nat, codomain nat, id int, name string) BinaryFunction[first, second, codomain] {
	if first < 0 || second < 0 || codomain < 0 { panic("smt: negative uninterpreted function sort identity") }
	return BinaryFunction[first, second, codomain].binaryFunctionValue(int(first), int(second), int(codomain), id, name)
}

func ApplyBinary(0 first nat, 0 second nat, 0 codomain nat, function BinaryFunction[first, second, codomain], left Term[UninterpretedSort[first]], right Term[UninterpretedSort[second]]) Term[UninterpretedSort[codomain]] {
	return Term[UninterpretedSort[codomain]].binaryApplication(function, left, right)
}

func DeclareRealUnaryFunction(id int, name string) SortedUnaryFunction[RealSort, RealSort] {
	return SortedUnaryFunction[RealSort, RealSort].sortedUnaryFunctionValue(-1, -1, id, name)
}

func ApplySortedUnary[D any, R any](function SortedUnaryFunction[D, R], argument Term[D]) Term[R] {
	return Term[R].sortedUnaryApplication(function, argument, -1)
}

func DeclareRealBinaryFunction(id int, name string) SortedBinaryFunction[RealSort, RealSort, RealSort] {
	return SortedBinaryFunction[RealSort, RealSort, RealSort].sortedBinaryFunctionValue(-1, -1, -1, id, name)
}

func ApplySortedBinary[A any, B any, R any](function SortedBinaryFunction[A, B, R], first Term[A], second Term[B]) Term[R] {
	return Term[R].sortedBinaryApplication(function, first, second, -1)
}

func DeclareBitVecUnaryFunction(domainWidth nat, rangeWidth nat, id int, name string) SortedUnaryFunction[BitVecSort[domainWidth], BitVecSort[rangeWidth]] {
	if domainWidth <= 0 || rangeWidth <= 0 { panic("smt: bit-vector function widths must be positive") }
	return SortedUnaryFunction[BitVecSort[domainWidth], BitVecSort[rangeWidth]].sortedUnaryFunctionValue(int(domainWidth), int(rangeWidth), id, name)
}

func ApplyBitVecUnary(0 domainWidth nat, 0 rangeWidth nat, function SortedUnaryFunction[BitVecSort[domainWidth], BitVecSort[rangeWidth]], argument Term[BitVecSort[domainWidth]]) Term[BitVecSort[rangeWidth]] {
	return Term[BitVecSort[rangeWidth]].sortedUnaryApplication(function, argument, 0)
}

func BitVecUnaryFunctionInfo[D any, R any](function SortedUnaryFunction[D, R]) (int, int, int) {
	match function { case sortedUnaryFunctionValue(domain, rangeKind, id, _): return domain, rangeKind, id }
}

func DeclareBitVecBinaryFunction(firstWidth nat, secondWidth nat, rangeWidth nat, id int, name string) SortedBinaryFunction[BitVecSort[firstWidth], BitVecSort[secondWidth], BitVecSort[rangeWidth]] {
	if firstWidth <= 0 || secondWidth <= 0 || rangeWidth <= 0 { panic("smt: bit-vector function widths must be positive") }
	return SortedBinaryFunction[BitVecSort[firstWidth], BitVecSort[secondWidth], BitVecSort[rangeWidth]].sortedBinaryFunctionValue(int(firstWidth), int(secondWidth), int(rangeWidth), id, name)
}

func ApplyBitVecBinary(0 firstWidth nat, 0 secondWidth nat, 0 rangeWidth nat, function SortedBinaryFunction[BitVecSort[firstWidth], BitVecSort[secondWidth], BitVecSort[rangeWidth]], first Term[BitVecSort[firstWidth]], second Term[BitVecSort[secondWidth]]) Term[BitVecSort[rangeWidth]] {
	return Term[BitVecSort[rangeWidth]].sortedBinaryApplication(function, first, second, 0)
}

func BitVecVal(width nat, value uint64) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVector(NewBitVectorUint64(int(width), value))
}

func BitVecConst(width nat, id int, name string) Term[BitVecSort[width]] {
	if width <= 0 { panic("smt: bit-vector width must be positive") }
	return Term[BitVecSort[width]].bitVectorSymbol(int(width), id, name)
}

func BitVecNot(0 width nat, value Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorNot(value)
}

func BitVecAnd(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorAnd(left, right)
}

func BitVecOr(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorOr(left, right)
}

func BitVecXor(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorXor(left, right)
}

func BitVecAdd(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorAdd(left, right)
}

func BitVecSub(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorSub(left, right)
}

func BitVecMul(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorMul(left, right)
}

func BitVecSHL(0 width nat, value Term[BitVecSort[width]], amount Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorShiftLeft(value, amount)
}

func BitVecLSHR(0 width nat, value Term[BitVecSort[width]], amount Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorLogicalShiftRight(value, amount)
}

func BitVecASHR(0 width nat, value Term[BitVecSort[width]], amount Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorArithmeticShiftRight(value, amount)
}

func BitVecUDiv(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorUnsignedDiv(left, right)
}

func BitVecURem(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorUnsignedRem(left, right)
}

func BitVecSDiv(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorSignedDiv(left, right)
}

func BitVecSRem(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	return Term[BitVecSort[width]].bitVectorSignedRem(left, right)
}

func BitVecConcat(firstWidth nat, secondWidth nat, first Term[BitVecSort[firstWidth]], second Term[BitVecSort[secondWidth]]) Term[BitVecSort[firstWidth+secondWidth]] {
	return Term[BitVecSort[firstWidth+secondWidth]].bitVectorConcat(first, second, int(firstWidth), int(secondWidth))
}

func BitVecExtract(high nat, low nat, 0 width nat, value Term[BitVecSort[width]]) Term[BitVecSort[high-low+1]] {
	if low < 0 || high < low { panic("smt: invalid bit-vector extraction range") }
	return Term[BitVecSort[high-low+1]].bitVectorExtract(value, int(high), int(low))
}

func BitVecZeroExtend(additional nat, 0 width nat, value Term[BitVecSort[width]]) Term[BitVecSort[width+additional]] {
	if additional < 0 { panic("smt: negative bit-vector extension") }
	return Term[BitVecSort[width+additional]].bitVectorZeroExtend(value, int(additional))
}

func BitVecSignExtend(additional nat, 0 width nat, value Term[BitVecSort[width]]) Term[BitVecSort[width+additional]] {
	if additional < 0 { panic("smt: negative bit-vector extension") }
	return Term[BitVecSort[width+additional]].bitVectorSignExtend(value, int(additional))
}

func BitVecRotateLeft(amount nat, 0 width nat, value Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	if amount < 0 { panic("smt: negative bit-vector rotation") }
	return Term[BitVecSort[width]].bitVectorRotateLeft(value, int(amount))
}

func BitVecRotateRight(amount nat, 0 width nat, value Term[BitVecSort[width]]) Term[BitVecSort[width]] {
	if amount < 0 { panic("smt: negative bit-vector rotation") }
	return Term[BitVecSort[width]].bitVectorRotateRight(value, int(amount))
}

func BitVecRepeat(count nat, 0 width nat, value Term[BitVecSort[width]]) Term[BitVecSort[width*count]] {
	if count <= 0 { panic("smt: bit-vector repeat count must be positive") }
	return Term[BitVecSort[width*count]].bitVectorRepeat(value, int(count))
}

func BitVecULT(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorUnsignedLess(left, right, false)
}

func BitVecULE(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorUnsignedLess(left, right, true)
}

func BitVecSLT(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorSignedLess(left, right, false)
}

func BitVecSLE(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorSignedLess(left, right, true)
}

func BitVecUAddOverflow(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorUnsignedAddOverflow(left, right)
}

func BitVecSAddOverflow(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorSignedAddOverflow(left, right)
}

func BitVecUSubOverflow(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorUnsignedSubOverflow(left, right)
}

func BitVecSSubOverflow(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorSignedSubOverflow(left, right)
}

func BitVecUMulOverflow(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorUnsignedMulOverflow(left, right)
}

func BitVecSMulOverflow(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorSignedMulOverflow(left, right)
}

func BitVecSDivOverflow(0 width nat, left Term[BitVecSort[width]], right Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorSignedDivOverflow(left, right)
}

func BitVecNegOverflow(0 width nat, value Term[BitVecSort[width]]) Term[BoolSort] {
	return Term[BoolSort].bitVectorNegOverflow(value)
}

func BitVecToNat(0 width nat, value Term[BitVecSort[width]]) Term[IntSort] {
	return Term[IntSort].bitVectorToInteger(value, false)
}

func BitVecToInt(0 width nat, value Term[BitVecSort[width]]) Term[IntSort] {
	return Term[IntSort].bitVectorToInteger(value, true)
}

func IntToBitVec(width nat, value Term[IntSort]) Term[BitVecSort[width]] {
	if width <= 0 { panic("smt: bit-vector width must be positive") }
	return Term[BitVecSort[width]].integerToBitVector(value, int(width))
}

func Assert(assertion nat, 0 c nat, 0 d nat, solver Solver[c, d], formula Term[BoolSort]) Solver[ContextID(c, assertion), d] {
	match solver {
	case solverValue(context, depth, state):
		if assertion < 0 { panic("smt: negative assertion identity") }
		nextContext := runtimeContextID(context, int(assertion))
		return solverValue(nextContext, depth, state.asserted(formula))
	}
}

func Push(0 c nat, 0 d nat, solver Solver[c, d]) Pushed[c, d] {
	match solver {
	case solverValue(context, depth, state):
		return PushResult(solverValue(context, depth+1, state), checkpointValue(context, depth, state))
	}
}

func Current(0 c nat, 0 d nat, pushed Pushed[c, d]) Solver[c, d+1] {
	match pushed { case PushResult(current, _): return current }
}

func Previous(0 c nat, 0 d nat, pushed Pushed[c, d]) Checkpoint[c, d] {
	match pushed { case PushResult(_, previous): return previous }
}

func Restore(0 current nat, 0 parent nat, 0 d nat, solver Solver[current, d+1], checkpoint Checkpoint[parent, d]) Solver[parent, d] {
	match solver {
	case solverValue(_, depth, _):
		match checkpoint {
		case checkpointValue(context, previousDepth, state):
			if depth != previousDepth+1 { panic("smt: checkpoint depth mismatch") }
			return solverValue(context, previousDepth, state)
		}
	}
}

func Check(0 c nat, 0 d nat, solver Solver[c, d]) CheckResult[c] {
	match solver {
	case solverValue(context, depth, state):
		if depth < 0 { panic("smt: invalid depth") }
		return runtimeCheckResult(context, state)
	}
}

// CheckAssuming solves with temporary Boolean assumptions. An unsatisfiable
// result carries a deletion-minimized set of indices into assumptions.
func CheckAssuming(0 c nat, 0 d nat, solver Solver[c, d], assumptions ...Term[BoolSort]) AssumptionCheckResult[c] {
	match solver {
	case solverValue(context, depth, state):
		if depth < 0 { panic("smt: invalid depth") }
		status, booleans, integers, reals, bitVectors, core, reason := state.checkAssuming(assumptions)
		switch status {
		case checkSat: return AssumptionsSatisfiable(modelValue(context, booleans, integers, reals, bitVectors, nil, nil, nil))
		case checkUnsat: return AssumptionsUnsatisfiable(proofValue(context, len(state.assertions)), core)
		default: return AssumptionsUnknown(proofValue(context, len(state.assertions)), reason)
		}
	}
}

func BoolValue(0 c nat, model Model[c], term Term[BoolSort]) (bool, bool) {
	match model { case modelValue(_, booleans, integers, reals, _, _, _, datatypes): return evaluateBoolWithDatatypes(term, booleans, integers, reals, datatypes) }
}

func IntValue(0 c nat, model Model[c], term Term[IntSort]) (int64, bool) {
	match model { case modelValue(_, booleans, integers, reals, _, _, _, _): return evaluateInt(term, booleans, integers, reals) }
}

func ExactIntValue(0 c nat, model Model[c], term Term[IntSort]) (IntegerValue, bool) {
	match model { case modelValue(_, booleans, integers, reals, bitVectors, _, _, _): return evaluateIntegerWithBitVectors(term, booleans, integers, reals, bitVectors) }
}

func IntegerModelValue(0 c nat, model Model[c], term Term[IntSort]) (IntegerValue, bool) {
	match model { case modelValue(_, booleans, integers, reals, bitVectors, arrays, _, _): return evaluateIntegerModelTerm(term, booleans, integers, reals, bitVectors, arrays) }
}

func RealValue(0 c nat, model Model[c], term Term[RealSort]) (Rational, bool) {
	match model { case modelValue(_, booleans, integers, reals, _, _, _, _): return evaluateReal(term, booleans, integers, reals) }
}

func BitVecModelValue(0 c nat, 0 width nat, model Model[c], term Term[BitVecSort[width]]) (BitVectorValue, bool) {
	match model { case modelValue(_, _, integers, _, bitVectors, _, arrays, _): return evaluateBitVectorModelTerm(term, bitVectors, integers, arrays) }
}

func IntegerArrayValue(0 c nat, model Model[c], array Term[ArraySort[IntSort, IntSort]], index IntegerValue) (IntegerValue, bool) {
	match model { case modelValue(_, _, integers, _, _, arrays, _, _): return evaluateIntegerArray(array, index, integers, arrays) }
}

func BitVectorArrayValue(0 c nat, 0 indexWidth nat, 0 elementWidth nat, model Model[c], array Term[ArraySort[BitVecSort[indexWidth], BitVecSort[elementWidth]]], index BitVectorValue) (BitVectorValue, bool) {
	match model { case modelValue(_, _, _, _, _, _, arrays, _): return evaluateBitVectorArray(array, index, arrays) }
}

func DatatypeModelValue(datatype nat, constructors nat, 0 c nat, model Model[c], term Term[DatatypeSort[datatype, constructors]]) (DatatypeValue, bool) {
	match model { case modelValue(_, _, _, _, _, _, _, datatypes): return evaluateDatatype(term, datatypes) }
}
