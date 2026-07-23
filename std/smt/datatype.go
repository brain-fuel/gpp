package smt

import (
	"reflect"
	"strconv"

	"goforge.dev/goplus/std/vec"
)

// NaryDatatypeSelectors is the compact erased representation of an indexed
// selector-name vector. Arity at most four requires no backing allocation.
type NaryDatatypeSelectors struct {
	Count    int
	Inline   [4]string
	Overflow []string
}

func compactNaryDatatypeSelectors(values vec.Vec[string]) NaryDatatypeSelectors {
	var result NaryDatatypeSelectors
	for {
		switch current := values.(type) {
		case vec.Nil[string]:
			return result
		case vec.Cons[string]:
			result.Append(current.Head)
			values = current.Tail
		default:
			panic("smt: invalid erased n-ary selector vector")
		}
	}
}

func (values *NaryDatatypeSelectors) Append(value string) {
	if values.Count < len(values.Inline) && values.Overflow == nil {
		values.Inline[values.Count] = value
		values.Count++
		return
	}
	if values.Overflow == nil {
		values.Overflow = append(make([]string, 0, values.Count+4), values.Inline[:]...)
	}
	values.Overflow = append(values.Overflow, value)
	values.Count++
}

func (values NaryDatatypeSelectors) Len() int { return values.Count }

func (values NaryDatatypeSelectors) At(index int) string {
	if index < 0 || index >= values.Count {
		panic("smt: n-ary selector outside arity")
	}
	if values.Overflow != nil {
		return values.Overflow[index]
	}
	return values.Inline[index]
}

// NaryDatatypeTerms is the compact erased representation of an indexed term
// vector. Arity at most four remains entirely inline.
type NaryDatatypeTerms struct {
	Count    int
	Inline   [4]Term[DatatypeSort]
	Overflow []Term[DatatypeSort]
}

func compactNaryDatatypeTerms[D any](values vec.Vec[Term[D]]) NaryDatatypeTerms {
	var result NaryDatatypeTerms
	for {
		switch current := values.(type) {
		case vec.Nil[Term[D]]:
			return result
		case vec.Cons[Term[D]]:
			term, ok := any(current.Head).(Term[DatatypeSort])
			if !ok {
				panic("smt: erased n-ary datatype term sort mismatch")
			}
			result.Append(term)
			values = current.Tail
		default:
			panic("smt: invalid erased n-ary datatype term vector")
		}
	}
}

func (values *NaryDatatypeTerms) Append(value Term[DatatypeSort]) {
	if values.Count < len(values.Inline) && values.Overflow == nil {
		values.Inline[values.Count] = value
		values.Count++
		return
	}
	if values.Overflow == nil {
		values.Overflow = append(make([]Term[DatatypeSort], 0, values.Count+4), values.Inline[:]...)
	}
	values.Overflow = append(values.Overflow, value)
	values.Count++
}

func (values NaryDatatypeTerms) Len() int { return values.Count }

func (values NaryDatatypeTerms) At(index int) Term[DatatypeSort] {
	if index < 0 || index >= values.Count {
		panic("smt: n-ary datatype term outside arity")
	}
	if values.Overflow != nil {
		return values.Overflow[index]
	}
	return values.Inline[index]
}

// DeclareNaryRecursiveDatatypeConstructorDynamic is the runtime-checked
// compatibility boundary for parsers and generated-Go façades that have
// already erased the arity index. Go+ callers should prefer the Vec-indexed
// DeclareNaryRecursiveDatatypeConstructor API.
func DeclareNaryRecursiveDatatypeConstructorDynamic(datatype, constructors, constructor int, name string, selectorNames []string) NaryRecursiveDatatypeConstructor {
	var names NaryDatatypeSelectors
	for _, selectorName := range selectorNames {
		names.Append(selectorName)
	}
	return DeclareNaryRecursiveDatatypeConstructorCompact(datatype, constructors, constructor, name, names)
}

// DeclareNaryRecursiveDatatypeConstructorCompact is the allocation-free
// erased boundary used by generated façades and SMT-LIB execution.
func DeclareNaryRecursiveDatatypeConstructorCompact(datatype, constructors, constructor int, name string, names NaryDatatypeSelectors) NaryRecursiveDatatypeConstructor {
	if constructors < 2 || constructor < 0 || constructor >= constructors {
		panic("smt: n-ary recursive constructor requires a possible base constructor inside datatype cardinality")
	}
	if names.Len() == 0 {
		panic("smt: n-ary recursive constructor requires at least one field")
	}
	for left := 0; left < names.Len(); left++ {
		for right := left + 1; right < names.Len(); right++ {
			if names.At(left) == names.At(right) {
				panic("smt: n-ary recursive constructor selectors must be distinct")
			}
		}
	}
	return naryRecursiveDatatypeConstructorValue{datatypeID: datatype, constructorCount: constructors, constructorID: constructor, arity: names.Len(), name: name, selectorNames: names}
}

// ApplyNaryRecursiveDatatypeConstructorDynamic checks erased arity and sort
// witnesses before retaining a normalized compact argument vector.
func ApplyNaryRecursiveDatatypeConstructorDynamic(declaration NaryRecursiveDatatypeConstructor, values []Term[DatatypeSort]) Term[DatatypeSort] {
	var terms NaryDatatypeTerms
	for _, value := range values {
		terms.Append(value)
	}
	return ApplyNaryRecursiveDatatypeConstructorCompact(declaration, terms)
}

// ApplyNaryRecursiveDatatypeConstructorCompact checks an erased compact term
// vector without introducing a backing slice for the common small arities.
func ApplyNaryRecursiveDatatypeConstructorCompact(declaration NaryRecursiveDatatypeConstructor, values NaryDatatypeTerms) Term[DatatypeSort] {
	witness := declaration
	if values.Len() != witness.arity {
		panic("smt: erased n-ary recursive datatype arity mismatch")
	}
	return datatypeNaryRecursiveApplication[DatatypeSort]{datatypeID: witness.datatypeID, constructorCount: witness.constructorCount, constructorID: witness.constructorID, arity: witness.arity, name: witness.name, selectorNames: witness.selectorNames, values: values}
}

// SelectNaryRecursiveDatatypeConstructorDynamic checks an erased field index.
func SelectNaryRecursiveDatatypeConstructorDynamic(field int, declaration NaryRecursiveDatatypeConstructor, value Term[DatatypeSort]) Term[DatatypeSort] {
	witness := declaration
	if field < 0 || field >= witness.arity {
		panic("smt: erased n-ary recursive datatype selector outside arity")
	}
	return datatypeNaryRecursiveSelector[DatatypeSort]{datatypeID: witness.datatypeID, constructorCount: witness.constructorCount, constructorID: witness.constructorID, arity: witness.arity, field: field, selectorName: witness.selectorNames.At(field), value: value}
}

// DatatypeValue is the exact model value of a supported algebraic datatype.
// IDs are declaration-local ordinals; ConstructorName is retained when the
// corresponding constructor appeared in the authored formula.
type DatatypeValue struct {
	DatatypeID       int
	ConstructorCount int
	ConstructorID    int
	ConstructorName  string
	Child            *DatatypeValue
	SecondChild      *DatatypeValue
	// Children is populated for arbitrary-arity recursive constructors. Unary
	// and binary values retain Child/SecondChild for source compatibility.
	Children *DatatypeChildren
	// Fields is populated for mixed-sort recursive constructors.
	Fields *DatatypeFields
}

// DatatypeChildren keeps the common arity-at-most-four case in one retained
// object while permitting arbitrary arity. DatatypeValue itself remains
// comparable because it contains only this pointer, preserving generated
// equality APIs in packages that embed model values.
type DatatypeChildren struct {
	Count    int
	Inline   [4]DatatypeValue
	Overflow []DatatypeValue
}

func newDatatypeChildren(values []DatatypeValue) *DatatypeChildren {
	children := &DatatypeChildren{Count: len(values)}
	if len(values) <= len(children.Inline) {
		copy(children.Inline[:], values)
	} else {
		children.Overflow = append([]DatatypeValue(nil), values...)
	}
	return children
}

func (children *DatatypeChildren) Len() int {
	if children == nil {
		return 0
	}
	return children.Count
}

func (children *DatatypeChildren) At(index int) (DatatypeValue, bool) {
	if children == nil || index < 0 || index >= children.Count {
		return DatatypeValue{}, false
	}
	if children.Overflow != nil {
		return children.Overflow[index], true
	}
	return children.Inline[index], true
}

type datatypeModelEntry struct {
	datatypeID int
	symbolID   int
	value      DatatypeValue
}

type datatypeModel struct {
	count                  int
	inline                 [8]datatypeModelEntry
	overflow               map[[2]int]DatatypeValue
	childCount             int
	children               *[8]DatatypeValue
	datatypeChildrenCount  int
	inlineDatatypeChildren [8]DatatypeChildren
	datatypeFieldsCount    int
	inlineDatatypeFields   [8]DatatypeFields
}

func (model *datatypeModel) retainDatatypeFields(count int) *DatatypeFields {
	if model.datatypeFieldsCount < len(model.inlineDatatypeFields) && count <= len(model.inlineDatatypeFields[0].Inline) {
		fields := &model.inlineDatatypeFields[model.datatypeFieldsCount]
		model.datatypeFieldsCount++
		fields.Count = count
		return fields
	}
	fields := &DatatypeFields{Count: count}
	if count > len(fields.Inline) {
		fields.Overflow = make([]DatatypeFieldValue, count)
	}
	return fields
}

func (model *datatypeModel) retainChild(value DatatypeValue) *DatatypeValue {
	if model.children == nil {
		model.children = new([8]DatatypeValue)
	}
	if model.childCount < len(*model.children) {
		child := &model.children[model.childCount]
		model.childCount++
		*child = value
		return child
	}
	child := new(DatatypeValue)
	*child = value
	return child
}

func (model *datatypeModel) retainDatatypeChildren(count int) *DatatypeChildren {
	if model.datatypeChildrenCount < len(model.inlineDatatypeChildren) && count <= len(model.inlineDatatypeChildren[0].Inline) {
		children := &model.inlineDatatypeChildren[model.datatypeChildrenCount]
		model.datatypeChildrenCount++
		children.Count = count
		return children
	}
	children := &DatatypeChildren{Count: count}
	if count > len(children.Inline) {
		children.Overflow = make([]DatatypeValue, count)
	}
	return children
}

func (children *DatatypeChildren) set(index int, value DatatypeValue) {
	if children.Overflow != nil {
		children.Overflow[index] = value
		return
	}
	children.Inline[index] = value
}

func (model *datatypeModel) set(datatypeID, symbolID int, value DatatypeValue) {
	for index := 0; index < model.count; index++ {
		if model.inline[index].datatypeID == datatypeID && model.inline[index].symbolID == symbolID {
			model.inline[index].value = value
			return
		}
	}
	if model.count < len(model.inline) {
		model.inline[model.count] = datatypeModelEntry{datatypeID: datatypeID, symbolID: symbolID, value: value}
		model.count++
		return
	}
	if model.overflow == nil {
		model.overflow = make(map[[2]int]DatatypeValue)
	}
	model.overflow[[2]int{datatypeID, symbolID}] = value
}

func (model *datatypeModel) lookup(datatypeID, symbolID int) (DatatypeValue, bool) {
	if model == nil {
		return DatatypeValue{}, false
	}
	for index := 0; index < model.count; index++ {
		entry := model.inline[index]
		if entry.datatypeID == datatypeID && entry.symbolID == symbolID {
			return entry.value, true
		}
	}
	value, ok := model.overflow[[2]int{datatypeID, symbolID}]
	return value, ok
}

func evaluateDatatype(term Term[DatatypeSort], model *datatypeModel) (DatatypeValue, bool) {
	switch value := term.(type) {
	case datatypeConstructor[DatatypeSort]:
		return DatatypeValue{DatatypeID: value.datatypeID, ConstructorCount: value.constructorCount, ConstructorID: value.constructorID, ConstructorName: value.name}, true
	case datatypeSymbol[DatatypeSort]:
		return model.lookup(value.datatypeID, value.iD)
	case datatypeRecursiveApplication[DatatypeSort]:
		child, ok := evaluateDatatype(value.value.(Term[DatatypeSort]), model)
		if !ok {
			return DatatypeValue{}, false
		}
		return DatatypeValue{DatatypeID: value.datatypeID, ConstructorCount: value.constructorCount, ConstructorID: value.constructorID, ConstructorName: value.name, Child: &child}, true
	case datatypeRecursiveSelector[DatatypeSort]:
		target, ok := value.value.(Term[DatatypeSort])
		if !ok {
			return DatatypeValue{}, false
		}
		if application, direct := target.(datatypeRecursiveApplication[DatatypeSort]); direct && application.datatypeID == value.datatypeID && application.constructorCount == value.constructorCount && application.constructorID == value.constructorID {
			return evaluateDatatype(application.value.(Term[DatatypeSort]), model)
		}
		modelValue, found := evaluateDatatype(target, model)
		if !found || modelValue.ConstructorID != value.constructorID || modelValue.Child == nil {
			return DatatypeValue{}, false
		}
		return *modelValue.Child, true
	case datatypeBinaryRecursiveApplication[DatatypeSort]:
		first, firstOK := evaluateDatatype(value.first.(Term[DatatypeSort]), model)
		second, secondOK := evaluateDatatype(value.second.(Term[DatatypeSort]), model)
		if !firstOK || !secondOK {
			return DatatypeValue{}, false
		}
		return DatatypeValue{DatatypeID: value.datatypeID, ConstructorCount: value.constructorCount, ConstructorID: value.constructorID, ConstructorName: value.name, Child: &first, SecondChild: &second}, true
	case datatypeBinaryRecursiveSelector[DatatypeSort]:
		target, ok := value.value.(Term[DatatypeSort])
		if !ok {
			return DatatypeValue{}, false
		}
		if application, direct := target.(datatypeBinaryRecursiveApplication[DatatypeSort]); direct && application.datatypeID == value.datatypeID && application.constructorCount == value.constructorCount && application.constructorID == value.constructorID {
			if value.field == 0 {
				return evaluateDatatype(application.first.(Term[DatatypeSort]), model)
			}
			return evaluateDatatype(application.second.(Term[DatatypeSort]), model)
		}
		modelValue, found := evaluateDatatype(target, model)
		if !found || modelValue.ConstructorID != value.constructorID || modelValue.Child == nil || modelValue.SecondChild == nil {
			return DatatypeValue{}, false
		}
		if value.field == 0 {
			return *modelValue.Child, true
		}
		return *modelValue.SecondChild, true
	case datatypeNaryRecursiveApplication[DatatypeSort]:
		children := make([]DatatypeValue, value.values.Len())
		for index := 0; index < value.values.Len(); index++ {
			item := value.values.At(index)
			child, ok := evaluateDatatype(item, model)
			if !ok {
				return DatatypeValue{}, false
			}
			children[index] = child
		}
		return DatatypeValue{DatatypeID: value.datatypeID, ConstructorCount: value.constructorCount, ConstructorID: value.constructorID, ConstructorName: value.name, Children: newDatatypeChildren(children)}, true
	case datatypeNaryRecursiveSelector[DatatypeSort]:
		target, ok := value.value.(Term[DatatypeSort])
		if !ok || value.field < 0 || value.field >= value.arity {
			return DatatypeValue{}, false
		}
		if application, direct := target.(datatypeNaryRecursiveApplication[DatatypeSort]); direct && application.datatypeID == value.datatypeID && application.constructorCount == value.constructorCount && application.constructorID == value.constructorID {
			if value.field < application.values.Len() {
				return evaluateDatatype(application.values.At(value.field), model)
			}
		}
		modelValue, found := evaluateDatatype(target, model)
		if !found || modelValue.ConstructorID != value.constructorID {
			return DatatypeValue{}, false
		}
		return modelValue.Children.At(value.field)
	case datatypeMixedSelector[DatatypeSort]:
		target, ok := value.value.(Term[DatatypeSort])
		if !ok || value.fieldKind != mixedDatatypeFieldSelf && value.fieldKind != mixedDatatypeFieldReference {
			return DatatypeValue{}, false
		}
		modelValue, found := evaluateDatatype(target, model)
		if !found || modelValue.ConstructorID != value.constructorID {
			return DatatypeValue{}, false
		}
		field, found := modelValue.Fields.At(value.field)
		if !found || field.Kind != value.fieldKind || field.Datatype == nil {
			return DatatypeValue{}, false
		}
		return *field.Datatype, true
	case datatypeMixedUpdate[DatatypeSort]:
		target, ok := value.value.(Term[DatatypeSort])
		if !ok {
			return DatatypeValue{}, false
		}
		modelValue, found := evaluateDatatype(target, model)
		if !found || modelValue.ConstructorID != value.constructorID {
			return modelValue, found
		}
		if modelValue.Fields == nil || value.field < 0 || value.field >= modelValue.Fields.Len() {
			return DatatypeValue{}, false
		}
		replacement, replacementOK := evaluateMixedUpdateReplacement(value.fieldKind, value.width, value.replacement, model)
		if !replacementOK {
			return DatatypeValue{}, false
		}
		fields := *modelValue.Fields
		if fields.Overflow != nil {
			fields.Overflow = append([]DatatypeFieldValue(nil), fields.Overflow...)
			fields.Overflow[value.field] = replacement
		} else {
			fields.Inline[value.field] = replacement
		}
		modelValue.Fields = &fields
		return modelValue, true
	default:
		return DatatypeValue{}, false
	}
}

func evaluateMixedUpdateReplacement(kind, width int, replacement any, datatypes *datatypeModel) (DatatypeFieldValue, bool) {
	result := DatatypeFieldValue{Kind: kind, Width: width}
	switch kind {
	case mixedDatatypeFieldBool:
		value, ok := evaluateBool(replacement.(Term[BoolSort]), booleanModel{}, integerModel{}, rationalModel{})
		result.Boolean = value
		return result, ok
	case mixedDatatypeFieldInt:
		value, ok := evaluateIntegerWithBitVectors(replacement.(Term[IntSort]), booleanModel{}, integerModel{}, rationalModel{}, bitVectorModel{})
		result.Integer = value
		return result, ok
	case mixedDatatypeFieldReal:
		value, ok := evaluateReal(replacement.(Term[RealSort]), booleanModel{}, integerModel{}, rationalModel{})
		result.Real = value
		return result, ok
	case mixedDatatypeFieldBitVec:
		value, ok := evaluateBitVector(replacement, bitVectorModel{}, integerModel{})
		result.BitVector = value
		return result, ok
	case mixedDatatypeFieldSelf, mixedDatatypeFieldReference:
		term, ok := replacement.(Term[DatatypeSort])
		if !ok {
			return DatatypeFieldValue{}, false
		}
		value, found := evaluateDatatype(term, datatypes)
		result.Datatype = &value
		return result, found
	default:
		return DatatypeFieldValue{}, false
	}
}

func evaluateBoolWithDatatypes(term Term[BoolSort], booleans booleanModel, integers integerModel, reals rationalModel, datatypes *datatypeModel) (bool, bool) {
	switch value := term.(type) {
	case datatypeRecognizer:
		candidate, ok := value.value.(Term[DatatypeSort])
		if !ok {
			return false, false
		}
		actual, found := evaluateDatatype(candidate, datatypes)
		return actual.ConstructorID == value.constructorID, found && actual.DatatypeID == value.datatypeID && actual.ConstructorCount == value.constructorCount
	case datatypeRecursiveRecognizer:
		candidate, ok := value.value.(Term[DatatypeSort])
		if !ok {
			return false, false
		}
		actual, found := evaluateDatatype(candidate, datatypes)
		return actual.ConstructorID == value.constructorID && actual.Child != nil, found && actual.DatatypeID == value.datatypeID && actual.ConstructorCount == value.constructorCount
	case datatypeBinaryRecursiveRecognizer:
		candidate, ok := value.value.(Term[DatatypeSort])
		if !ok {
			return false, false
		}
		actual, found := evaluateDatatype(candidate, datatypes)
		return actual.ConstructorID == value.constructorID && actual.Child != nil && actual.SecondChild != nil, found && actual.DatatypeID == value.datatypeID && actual.ConstructorCount == value.constructorCount
	case datatypeNaryRecursiveRecognizer:
		candidate, ok := value.value.(Term[DatatypeSort])
		if !ok {
			return false, false
		}
		actual, found := evaluateDatatype(candidate, datatypes)
		return actual.ConstructorID == value.constructorID && actual.Children.Len() == value.arity, found && actual.DatatypeID == value.datatypeID && actual.ConstructorCount == value.constructorCount
	case datatypeMixedRecognizer:
		candidate, ok := value.value.(Term[DatatypeSort])
		if !ok {
			return false, false
		}
		actual, found := evaluateDatatype(candidate, datatypes)
		return actual.ConstructorID == value.constructorID && actual.Fields.Len() == value.specs.Len(), found && actual.DatatypeID == value.datatypeID && actual.ConstructorCount == value.constructorCount
	case Equal:
		left, leftOK := value.Left.(Term[DatatypeSort])
		right, rightOK := value.Right.(Term[DatatypeSort])
		if leftOK && rightOK {
			leftValue, leftFound := evaluateDatatype(left, datatypes)
			rightValue, rightFound := evaluateDatatype(right, datatypes)
			return equalDatatypeValue(leftValue, rightValue), leftFound && rightFound
		}
	case Not:
		result, ok := evaluateBoolWithDatatypes(value.Value, booleans, integers, reals, datatypes)
		return !result, ok
	case And:
		for _, item := range value.Values {
			result, ok := evaluateBoolWithDatatypes(item, booleans, integers, reals, datatypes)
			if !ok || !result {
				return result, ok
			}
		}
		return true, true
	case BooleanConjunction:
		items, negated := value.values()
		for index, item := range items {
			result, ok := evaluateBoolWithDatatypes(item, booleans, integers, reals, datatypes)
			if !ok || result == negated[index] {
				return false, ok
			}
		}
		return true, true
	case Or:
		for _, item := range value.Values {
			result, ok := evaluateBoolWithDatatypes(item, booleans, integers, reals, datatypes)
			if !ok {
				return false, false
			}
			if result {
				return true, true
			}
		}
		return false, true
	case Implies:
		left, leftOK := evaluateBoolWithDatatypes(value.Left, booleans, integers, reals, datatypes)
		right, rightOK := evaluateBoolWithDatatypes(value.Right, booleans, integers, reals, datatypes)
		return !left || right, leftOK && rightOK
	case Iff:
		left, leftOK := evaluateBoolWithDatatypes(value.Left, booleans, integers, reals, datatypes)
		right, rightOK := evaluateBoolWithDatatypes(value.Right, booleans, integers, reals, datatypes)
		return left == right, leftOK && rightOK
	}
	return evaluateBool(term, booleans, integers, reals)
}

func equalDatatypeValue(left, right DatatypeValue) bool {
	if left.DatatypeID != right.DatatypeID || left.ConstructorCount != right.ConstructorCount || left.ConstructorID != right.ConstructorID || (left.Child == nil) != (right.Child == nil) || (left.SecondChild == nil) != (right.SecondChild == nil) || left.Children.Len() != right.Children.Len() || left.Fields.Len() != right.Fields.Len() {
		return false
	}
	if left.Child != nil && !equalDatatypeValue(*left.Child, *right.Child) {
		return false
	}
	if left.SecondChild != nil && !equalDatatypeValue(*left.SecondChild, *right.SecondChild) {
		return false
	}
	for index := 0; index < left.Children.Len(); index++ {
		leftChild, _ := left.Children.At(index)
		rightChild, _ := right.Children.At(index)
		if !equalDatatypeValue(leftChild, rightChild) {
			return false
		}
	}
	for index := 0; index < left.Fields.Len(); index++ {
		leftField, _ := left.Fields.At(index)
		rightField, _ := right.Fields.At(index)
		if !equalDatatypeFieldValue(leftField, rightField) {
			return false
		}
	}
	return true
}

func equalDatatypeFieldValue(left, right DatatypeFieldValue) bool {
	if left.Kind != right.Kind || left.Width != right.Width {
		return false
	}
	switch left.Kind {
	case mixedDatatypeFieldBool:
		return left.Boolean == right.Boolean
	case mixedDatatypeFieldInt:
		return CompareIntegerValue(left.Integer, right.Integer) == 0
	case mixedDatatypeFieldReal:
		return CompareRational(left.Real, right.Real) == 0
	case mixedDatatypeFieldBitVec:
		return EqualBitVectorValue(left.BitVector, right.BitVector)
	case mixedDatatypeFieldSelf, mixedDatatypeFieldReference:
		return left.Datatype != nil && right.Datatype != nil && equalDatatypeValue(*left.Datatype, *right.Datatype)
	default:
		return false
	}
}

type datatypeNode struct {
	datatypeID       int
	constructorCount int
	kind             uint8
	id               int
	name             string
	child            int
	second           int
	field            int
	children         datatypeNodeChildren
	mixedSpecs       MixedDatatypeFieldSpecs
	mixedValues      MixedDatatypeTermValues
	mixedChildren    datatypeNodeChildren
	mixedReplacement MixedDatatypeTermValue
}

type datatypeNodeChildren struct {
	count    int
	inline   [4]int
	overflow []int
}

func (children *datatypeNodeChildren) append(value int) {
	if children.count < len(children.inline) && children.overflow == nil {
		children.inline[children.count] = value
		children.count++
		return
	}
	if children.overflow == nil {
		children.overflow = append(make([]int, 0, children.count+4), children.inline[:]...)
	}
	children.overflow = append(children.overflow, value)
	children.count++
}

func (children datatypeNodeChildren) len() int { return children.count }

func (children datatypeNodeChildren) at(index int) int {
	if children.overflow != nil {
		return children.overflow[index]
	}
	return children.inline[index]
}

type datatypePair struct{ left, right int }
type datatypeTagConstraint struct {
	node        int
	constructor int
	negated     bool
	recursive   bool
	nary        bool
	arity       int
	name        string
	mixedSpecs  MixedDatatypeFieldSpecs
}

func (value datatypeMixedSelector[S]) mixedSelectorSchema() datatypeTagConstraint {
	return datatypeTagConstraint{
		constructor: value.constructorID,
		recursive:   true,
		nary:        true,
		arity:       value.specs.Len(),
		name:        value.constructorName,
		mixedSpecs:  value.specs,
	}
}

type datatypeProblem struct {
	nodes                 []datatypeNode
	parents               []int
	ranks                 []uint8
	disequalities         []datatypePair
	tags                  []datatypeTagConstraint
	unsat                 bool
	inlineNodes           [8]datatypeNode
	inlineParents         [8]int
	inlineRanks           [8]uint8
	inlineDisequalities   [8]datatypePair
	inlineTags            [8]datatypeTagConstraint
	model                 datatypeModel
	mixedEqualities       []Term[BoolSort]
	mixedAssertions       []Term[BoolSort]
	matchTags             []datatypeTagConstraint
	inlineMixedEqualities [8]Term[BoolSort]
	inlineMixedAssertions [8]Term[BoolSort]
	scalarOutcome         checkOutcome
	assignment            []int
}

func containsDatatypeTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case Equal:
		return isDatatypeTerm(value.Left) || isDatatypeTerm(value.Right) || isMixedDatatypeSelector(value.Left) || isMixedDatatypeSelector(value.Right) || isMixedScalarDatatypeSelector(value.Left) || isMixedScalarDatatypeSelector(value.Right)
	case datatypeRecognizer, datatypeRecursiveRecognizer, datatypeBinaryRecursiveRecognizer, datatypeNaryRecursiveRecognizer, datatypeMixedRecognizer:
		return true
	case Not:
		return containsDatatypeTheory(value.Value)
	case And:
		for _, item := range value.Values {
			if containsDatatypeTheory(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsDatatypeTheory(item) {
				return true
			}
		}
	}
	return false
}

func isDatatypeTerm(term any) bool {
	switch term.(type) {
	case datatypeSymbol[DatatypeSort], datatypeConstructor[DatatypeSort], datatypeRecursiveApplication[DatatypeSort], datatypeRecursiveSelector[DatatypeSort], datatypeBinaryRecursiveApplication[DatatypeSort], datatypeBinaryRecursiveSelector[DatatypeSort], datatypeNaryRecursiveApplication[DatatypeSort], datatypeNaryRecursiveSelector[DatatypeSort], datatypeMixedApplication[DatatypeSort], datatypeMixedSelector[DatatypeSort], datatypeMixedUpdate[DatatypeSort]:
		return true
	default:
		return false
	}
}

func isMixedDatatypeSelector(term any) bool {
	switch term.(type) {
	case datatypeMixedSelector[BoolSort], datatypeMixedSelector[IntSort], datatypeMixedSelector[RealSort], datatypeMixedSelector[BitVecSort], datatypeMixedSelector[DatatypeSort]:
		return true
	default:
		return false
	}
}

func isMixedScalarDatatypeSelector(term any) bool {
	switch value := term.(type) {
	case datatypeMixedSelector[BoolSort], datatypeMixedSelector[IntSort], datatypeMixedSelector[RealSort], datatypeMixedSelector[BitVecSort]:
		return true
	case If[IntSort]:
		return containsMixedDatatypeTheory(value.Condition) || isMixedScalarDatatypeSelector(value.Then) || isMixedScalarDatatypeSelector(value.Else)
	case If[RealSort]:
		return containsMixedDatatypeTheory(value.Condition) || isMixedScalarDatatypeSelector(value.Then) || isMixedScalarDatatypeSelector(value.Else)
	case If[BoolSort]:
		return containsMixedDatatypeTheory(value.Condition) || isMixedScalarDatatypeSelector(value.Then) || isMixedScalarDatatypeSelector(value.Else)
	default:
		return false
	}
}

func containsMixedDatatypeTheory(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case Equal:
		return isMixedDatatypeSelector(value.Left) || isMixedDatatypeSelector(value.Right) || isMixedScalarDatatypeSelector(value.Left) || isMixedScalarDatatypeSelector(value.Right) || isMixedDatatypeApplication(value.Left) || isMixedDatatypeApplication(value.Right)
	case datatypeMixedRecognizer:
		return true
	case And:
		for _, item := range value.Values {
			if containsMixedDatatypeTheory(item) {
				return true
			}
		}
	case BooleanConjunction:
		items, _ := value.values()
		for _, item := range items {
			if containsMixedDatatypeTheory(item) {
				return true
			}
		}
	case Not:
		return containsMixedDatatypeTheory(value.Value)
	}
	return false
}

func isMixedDatatypeApplication(term any) bool {
	_, ok := term.(datatypeMixedApplication[DatatypeSort])
	return ok
}

func solveDatatypeAssertions(assertions []Term[BoolSort]) (checkOutcome, bool) {
	problem := datatypeProblem{}
	problem.nodes = problem.inlineNodes[:0]
	problem.parents = problem.inlineParents[:0]
	problem.ranks = problem.inlineRanks[:0]
	problem.disequalities = problem.inlineDisequalities[:0]
	problem.tags = problem.inlineTags[:0]
	problem.mixedEqualities = problem.inlineMixedEqualities[:0]
	problem.mixedAssertions = problem.inlineMixedAssertions[:0]
	for _, assertion := range assertions {
		if !problem.boolean(assertion, false) {
			return checkOutcome{}, false
		}
	}
	if problem.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	return problem.solve()
}

func (problem *datatypeProblem) boolean(term Term[BoolSort], negated bool) bool {
	switch value := term.(type) {
	case Bool:
		problem.unsat = problem.unsat || value.Value == negated
		return true
	case And:
		if negated {
			return false
		}
		for _, item := range value.Values {
			if !problem.boolean(item, false) {
				return false
			}
		}
		return true
	case BooleanConjunction:
		if negated {
			return false
		}
		items, polarities := value.values()
		for index, item := range items {
			if !problem.boolean(item, polarities[index]) {
				return false
			}
		}
		return true
	case Not:
		return problem.boolean(value.Value, !negated)
	case Equal:
		if isMixedScalarDatatypeSelector(value.Left) || isMixedScalarDatatypeSelector(value.Right) {
			if !problem.retainMixedScalarSelectorTarget(value.Left) || !problem.retainMixedScalarSelectorTarget(value.Right) {
				return false
			}
			assertion := term
			if negated {
				assertion = Not{Value: term}
			}
			problem.mixedAssertions = append(problem.mixedAssertions, assertion)
			return true
		}
		left, leftOK := problem.term(value.Left)
		right, rightOK := problem.term(value.Right)
		if !leftOK || !rightOK || !problem.compatible(left, right) {
			return false
		}
		if negated {
			problem.disequalities = append(problem.disequalities, datatypePair{left: left, right: right})
		} else {
			problem.union(left, right)
		}
		return true
	case datatypeRecognizer:
		candidate, ok := problem.term(value.value)
		if !ok || problem.nodes[candidate].datatypeID != value.datatypeID || problem.nodes[candidate].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return false
		}
		candidateNode := problem.nodes[candidate]
		if isDatatypeConstructorNode(candidateNode) {
			matches := candidateNode.id == value.constructorID
			problem.unsat = problem.unsat || matches == negated
			return true
		}
		problem.tags = append(problem.tags, datatypeTagConstraint{node: candidate, constructor: value.constructorID, negated: negated})
		return true
	case datatypeRecursiveRecognizer:
		candidate, ok := problem.term(value.value)
		if !ok || problem.nodes[candidate].datatypeID != value.datatypeID || problem.nodes[candidate].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return false
		}
		candidateNode := problem.nodes[candidate]
		if isDatatypeConstructorNode(candidateNode) {
			matches := candidateNode.kind == 2 && candidateNode.id == value.constructorID
			problem.unsat = problem.unsat || matches == negated
			return true
		}
		problem.tags = append(problem.tags, datatypeTagConstraint{node: candidate, constructor: value.constructorID, negated: negated, recursive: true, arity: 1, name: value.name})
		return true
	case datatypeBinaryRecursiveRecognizer:
		candidate, ok := problem.term(value.value)
		if !ok || problem.nodes[candidate].datatypeID != value.datatypeID || problem.nodes[candidate].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return false
		}
		candidateNode := problem.nodes[candidate]
		if isDatatypeConstructorNode(candidateNode) {
			matches := candidateNode.kind == 4 && candidateNode.id == value.constructorID
			problem.unsat = problem.unsat || matches == negated
			return true
		}
		problem.tags = append(problem.tags, datatypeTagConstraint{node: candidate, constructor: value.constructorID, negated: negated, recursive: true, arity: 2, name: value.name})
		return true
	case datatypeNaryRecursiveRecognizer:
		candidate, ok := problem.term(value.value)
		if !ok || problem.nodes[candidate].datatypeID != value.datatypeID || problem.nodes[candidate].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount || value.arity <= 0 {
			return false
		}
		candidateNode := problem.nodes[candidate]
		if isDatatypeConstructorNode(candidateNode) {
			matches := candidateNode.kind == 6 && candidateNode.id == value.constructorID && candidateNode.children.len() == value.arity
			problem.unsat = problem.unsat || matches == negated
			return true
		}
		problem.tags = append(problem.tags, datatypeTagConstraint{node: candidate, constructor: value.constructorID, negated: negated, recursive: true, nary: true, arity: value.arity, name: value.name})
		return true
	case datatypeMixedRecognizer:
		candidate, ok := problem.term(value.value)
		if !ok || problem.nodes[candidate].datatypeID != value.datatypeID || problem.nodes[candidate].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount || value.specs.Len() == 0 {
			return false
		}
		candidateNode := problem.nodes[candidate]
		if isDatatypeConstructorNode(candidateNode) {
			matches := candidateNode.kind == 8 && candidateNode.id == value.constructorID
			problem.unsat = problem.unsat || matches == negated
			return true
		}
		problem.tags = append(problem.tags, datatypeTagConstraint{node: candidate, constructor: value.constructorID, negated: negated, recursive: true, nary: true, arity: value.specs.Len(), name: value.name, mixedSpecs: value.specs})
		return true
	default:
		return false
	}
}

func (problem *datatypeProblem) retainMixedScalarSelectorTarget(term any) bool {
	switch value := term.(type) {
	case datatypeMixedSelector[BoolSort]:
		node, ok := problem.term(value.value)
		problem.retainMixedSelectorSchema(node, ok, value)
		return ok
	case datatypeMixedSelector[IntSort]:
		node, ok := problem.term(value.value)
		problem.retainMixedSelectorSchema(node, ok, value)
		return ok
	case datatypeMixedSelector[RealSort]:
		node, ok := problem.term(value.value)
		problem.retainMixedSelectorSchema(node, ok, value)
		return ok
	case datatypeMixedSelector[BitVecSort]:
		node, ok := problem.term(value.value)
		problem.retainMixedSelectorSchema(node, ok, value)
		return ok
	case If[IntSort]:
		return problem.retainMixedBooleanTargets(value.Condition) && problem.retainMixedScalarSelectorTarget(value.Then) && problem.retainMixedScalarSelectorTarget(value.Else)
	case If[RealSort]:
		return problem.retainMixedBooleanTargets(value.Condition) && problem.retainMixedScalarSelectorTarget(value.Then) && problem.retainMixedScalarSelectorTarget(value.Else)
	case If[BoolSort]:
		return problem.retainMixedBooleanTargets(value.Condition) && problem.retainMixedScalarSelectorTarget(value.Then) && problem.retainMixedScalarSelectorTarget(value.Else)
	default:
		return true
	}
}

func (problem *datatypeProblem) retainMixedSelectorSchema(node int, ok bool, value interface {
	mixedSelectorSchema() datatypeTagConstraint
}) {
	if !ok {
		return
	}
	tag := value.mixedSelectorSchema()
	tag.node = node
	problem.matchTags = append(problem.matchTags, tag)
}

func (problem *datatypeProblem) retainMixedBooleanTargets(term Term[BoolSort]) bool {
	switch value := term.(type) {
	case datatypeRecognizer:
		node, ok := problem.term(value.value)
		if ok {
			problem.matchTags = append(problem.matchTags, datatypeTagConstraint{node: node, constructor: value.constructorID})
		}
		return ok
	case datatypeRecursiveRecognizer:
		node, ok := problem.term(value.value)
		if ok {
			problem.matchTags = append(problem.matchTags, datatypeTagConstraint{node: node, constructor: value.constructorID, recursive: true, arity: 1, name: value.name})
		}
		return ok
	case datatypeBinaryRecursiveRecognizer:
		node, ok := problem.term(value.value)
		if ok {
			problem.matchTags = append(problem.matchTags, datatypeTagConstraint{node: node, constructor: value.constructorID, recursive: true, arity: 2, name: value.name})
		}
		return ok
	case datatypeNaryRecursiveRecognizer:
		node, ok := problem.term(value.value)
		if ok {
			problem.matchTags = append(problem.matchTags, datatypeTagConstraint{node: node, constructor: value.constructorID, recursive: true, nary: true, arity: value.arity, name: value.name})
		}
		return ok
	case datatypeMixedRecognizer:
		node, ok := problem.term(value.value)
		if ok {
			problem.matchTags = append(problem.matchTags, datatypeTagConstraint{node: node, constructor: value.constructorID, recursive: true, nary: true, arity: value.specs.Len(), name: value.name, mixedSpecs: value.specs})
		}
		return ok
	case Not:
		return problem.retainMixedBooleanTargets(value.Value)
	default:
		return true
	}
}

func (problem *datatypeProblem) term(term any) (int, bool) {
	switch value := term.(type) {
	case datatypeSymbol[DatatypeSort]:
		if value.constructorCount <= 0 {
			return 0, false
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, id: value.iD, name: value.name}), true
	case datatypeConstructor[DatatypeSort]:
		if value.constructorCount <= 0 || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return 0, false
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 1, id: value.constructorID, name: value.name}), true
	case datatypeRecursiveApplication[DatatypeSort]:
		child, ok := problem.term(value.value)
		if !ok || problem.nodes[child].datatypeID != value.datatypeID || problem.nodes[child].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return 0, false
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 2, id: value.constructorID, name: value.name, child: child}), true
	case datatypeRecursiveSelector[DatatypeSort]:
		target, ok := problem.term(value.value)
		if !ok || problem.nodes[target].datatypeID != value.datatypeID || problem.nodes[target].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return 0, false
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 3, id: value.constructorID, name: value.selectorName, child: target}), true
	case datatypeBinaryRecursiveApplication[DatatypeSort]:
		first, firstOK := problem.term(value.first)
		second, secondOK := problem.term(value.second)
		if !firstOK || !secondOK || problem.nodes[first].datatypeID != value.datatypeID || problem.nodes[first].constructorCount != value.constructorCount || problem.nodes[second].datatypeID != value.datatypeID || problem.nodes[second].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return 0, false
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 4, id: value.constructorID, name: value.name, child: first, second: second}), true
	case datatypeBinaryRecursiveSelector[DatatypeSort]:
		target, ok := problem.term(value.value)
		if !ok || problem.nodes[target].datatypeID != value.datatypeID || problem.nodes[target].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount || value.field < 0 || value.field >= 2 {
			return 0, false
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 5, id: value.constructorID, name: value.selectorName, child: target, field: value.field}), true
	case datatypeNaryRecursiveApplication[DatatypeSort]:
		if value.arity <= 0 || value.values.Len() != value.arity || value.selectorNames.Len() != value.arity || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return 0, false
		}
		var children datatypeNodeChildren
		for index := 0; index < value.values.Len(); index++ {
			item := value.values.At(index)
			child, ok := problem.term(item)
			if !ok || problem.nodes[child].datatypeID != value.datatypeID || problem.nodes[child].constructorCount != value.constructorCount {
				return 0, false
			}
			children.append(child)
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 6, id: value.constructorID, name: value.name, children: children}), true
	case datatypeNaryRecursiveSelector[DatatypeSort]:
		target, ok := problem.term(value.value)
		if !ok || problem.nodes[target].datatypeID != value.datatypeID || problem.nodes[target].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount || value.arity <= 0 || value.field < 0 || value.field >= value.arity {
			return 0, false
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 7, id: value.constructorID, name: value.selectorName, child: target, field: value.field}), true
	case datatypeMixedApplication[DatatypeSort]:
		if value.specs.Len() == 0 || value.specs.Len() != value.values.Len() || value.constructorID < 0 || value.constructorID >= value.constructorCount {
			return 0, false
		}
		var selfChildren datatypeNodeChildren
		for field := 0; field < value.specs.Len(); field++ {
			spec, argument := value.specs.At(field), value.values.At(field)
			if spec.Kind != argument.Kind || spec.Width != argument.Width || spec.DatatypeID != argument.DatatypeID || spec.ConstructorCount != argument.ConstructorCount {
				return 0, false
			}
			if spec.Kind != mixedDatatypeFieldSelf && spec.Kind != mixedDatatypeFieldReference {
				continue
			}
			child, ok := problem.term(argument.Term)
			expectedDatatype, expectedConstructors := value.datatypeID, value.constructorCount
			if spec.Kind == mixedDatatypeFieldReference {
				expectedDatatype, expectedConstructors = spec.DatatypeID, spec.ConstructorCount
			}
			if !ok || problem.nodes[child].datatypeID != expectedDatatype || problem.nodes[child].constructorCount != expectedConstructors {
				return 0, false
			}
			selfChildren.append(child)
		}
		return problem.ensure(datatypeNode{datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 8, id: value.constructorID, name: value.name, mixedSpecs: value.specs, mixedValues: value.values, mixedChildren: selfChildren}), true
	case datatypeMixedSelector[DatatypeSort]:
		if value.fieldKind != mixedDatatypeFieldSelf && value.fieldKind != mixedDatatypeFieldReference {
			return 0, false
		}
		target, ok := problem.term(value.value)
		if !ok || problem.nodes[target].datatypeID != value.datatypeID || problem.nodes[target].constructorCount != value.constructorCount || value.constructorID < 0 || value.constructorID >= value.constructorCount || value.field < 0 {
			return 0, false
		}
		resultDatatype, resultConstructors := value.datatypeID, value.constructorCount
		if value.fieldKind == mixedDatatypeFieldReference {
			if value.targetDatatypeID < 0 || value.targetConstructorCount <= 0 {
				return 0, false
			}
			resultDatatype, resultConstructors = value.targetDatatypeID, value.targetConstructorCount
		}
		return problem.ensure(datatypeNode{datatypeID: resultDatatype, constructorCount: resultConstructors, kind: 9, id: value.constructorID, name: value.selectorName, child: target, field: value.field}), true
	case datatypeMixedUpdate[DatatypeSort]:
		if value.constructorID < 0 || value.constructorID >= value.constructorCount || value.field < 0 || value.field >= value.specs.Len() {
			return 0, false
		}
		spec := value.specs.At(value.field)
		if spec.Kind != value.fieldKind || spec.Width != value.width || spec.DatatypeID != value.targetDatatypeID || spec.ConstructorCount != value.targetConstructorCount {
			return 0, false
		}
		target, ok := problem.term(value.value)
		if !ok || problem.nodes[target].datatypeID != value.datatypeID || problem.nodes[target].constructorCount != value.constructorCount {
			return 0, false
		}
		replacement := MixedDatatypeTermValue{
			Kind: value.fieldKind, Width: value.width, Term: value.replacement,
			DatatypeID: value.targetDatatypeID, ConstructorCount: value.targetConstructorCount,
		}
		if value.fieldKind == mixedDatatypeFieldSelf || value.fieldKind == mixedDatatypeFieldReference {
			child, childOK := problem.term(value.replacement)
			expectedDatatype, expectedConstructors := value.datatypeID, value.constructorCount
			if value.fieldKind == mixedDatatypeFieldReference {
				expectedDatatype, expectedConstructors = value.targetDatatypeID, value.targetConstructorCount
			}
			if !childOK || problem.nodes[child].datatypeID != expectedDatatype || problem.nodes[child].constructorCount != expectedConstructors {
				return 0, false
			}
		}
		return problem.ensure(datatypeNode{
			datatypeID: value.datatypeID, constructorCount: value.constructorCount, kind: 10,
			id: value.constructorID, child: target, field: value.field, mixedSpecs: value.specs,
			mixedReplacement: replacement,
		}), true
	default:
		return 0, false
	}
}

func (problem *datatypeProblem) ensure(node datatypeNode) int {
	for index, existing := range problem.nodes {
		samePayload := true
		switch node.kind {
		case 2, 3:
			samePayload = existing.child == node.child
		case 4:
			samePayload = existing.child == node.child && existing.second == node.second
		case 5:
			samePayload = existing.child == node.child && existing.field == node.field
		case 6:
			samePayload = existing.children.len() == node.children.len()
			if samePayload {
				for field := 0; field < node.children.len(); field++ {
					if existing.children.at(field) != node.children.at(field) {
						samePayload = false
						break
					}
				}
			}
		case 7:
			samePayload = existing.child == node.child && existing.field == node.field
		case 8:
			samePayload = sameMixedDatatypeFields(existing.mixedSpecs, node.mixedSpecs, existing.mixedValues, node.mixedValues)
		case 9:
			samePayload = existing.child == node.child && existing.field == node.field
		case 10:
			samePayload = existing.child == node.child && existing.field == node.field &&
				reflect.DeepEqual(existing.mixedReplacement, node.mixedReplacement)
		}
		if existing.datatypeID == node.datatypeID && existing.constructorCount == node.constructorCount && existing.kind == node.kind && existing.id == node.id && samePayload {
			if problem.nodes[index].name == "" {
				problem.nodes[index].name = node.name
			}
			return index
		}
	}
	index := len(problem.nodes)
	problem.nodes = append(problem.nodes, node)
	problem.parents = append(problem.parents, index)
	problem.ranks = append(problem.ranks, 0)
	return index
}

func sameMixedDatatypeFields(leftSpecs, rightSpecs MixedDatatypeFieldSpecs, leftValues, rightValues MixedDatatypeTermValues) bool {
	if leftSpecs.Len() != rightSpecs.Len() || leftValues.Len() != rightValues.Len() || leftSpecs.Len() != leftValues.Len() {
		return false
	}
	for index := 0; index < leftSpecs.Len(); index++ {
		if leftSpecs.At(index) != rightSpecs.At(index) {
			return false
		}
		left, right := leftValues.At(index), rightValues.At(index)
		if left.Kind != right.Kind || left.Width != right.Width || !reflect.DeepEqual(left.Term, right.Term) {
			return false
		}
	}
	return true
}

func (problem *datatypeProblem) compatible(left, right int) bool {
	return problem.nodes[left].datatypeID == problem.nodes[right].datatypeID && problem.nodes[left].constructorCount == problem.nodes[right].constructorCount
}

func (problem *datatypeProblem) find(node int) int {
	root := node
	for problem.parents[root] != root {
		root = problem.parents[root]
	}
	for problem.parents[node] != node {
		next := problem.parents[node]
		problem.parents[node] = root
		node = next
	}
	return root
}

func (problem *datatypeProblem) union(left, right int) {
	left, right = problem.find(left), problem.find(right)
	if left == right {
		return
	}
	leftNode, rightNode := problem.nodes[left], problem.nodes[right]
	leftConstructor, rightConstructor := isDatatypeConstructorNode(leftNode), isDatatypeConstructorNode(rightNode)
	if !problem.compatible(left, right) || leftConstructor && rightConstructor && (leftNode.id != rightNode.id || leftNode.kind != rightNode.kind) {
		problem.unsat = true
		return
	}
	if leftNode.kind == 2 && rightNode.kind == 2 {
		problem.union(leftNode.child, rightNode.child)
		if problem.unsat {
			return
		}
	}
	if leftNode.kind == 4 && rightNode.kind == 4 {
		problem.union(leftNode.child, rightNode.child)
		if problem.unsat {
			return
		}
		problem.union(leftNode.second, rightNode.second)
		if problem.unsat {
			return
		}
	}
	if leftNode.kind == 6 && rightNode.kind == 6 {
		if leftNode.children.len() != rightNode.children.len() {
			problem.unsat = true
			return
		}
		for field := 0; field < leftNode.children.len(); field++ {
			problem.union(leftNode.children.at(field), rightNode.children.at(field))
			if problem.unsat {
				return
			}
		}
	}
	if leftNode.kind == 8 && rightNode.kind == 8 {
		if leftNode.mixedSpecs.Len() != rightNode.mixedSpecs.Len() {
			problem.unsat = true
			return
		}
		self := 0
		for field := 0; field < leftNode.mixedSpecs.Len(); field++ {
			leftSpec, rightSpec := leftNode.mixedSpecs.At(field), rightNode.mixedSpecs.At(field)
			if leftSpec.Kind != rightSpec.Kind || leftSpec.Width != rightSpec.Width {
				problem.unsat = true
				return
			}
			if leftSpec.Kind == mixedDatatypeFieldSelf || leftSpec.Kind == mixedDatatypeFieldReference {
				problem.union(leftNode.mixedChildren.at(self), rightNode.mixedChildren.at(self))
				self++
				if problem.unsat {
					return
				}
				continue
			}
			problem.mixedEqualities = append(problem.mixedEqualities, Equal{Left: leftNode.mixedValues.At(field).Term, Right: rightNode.mixedValues.At(field).Term})
		}
	}
	if problem.ranks[left] < problem.ranks[right] {
		left, right = right, left
	}
	problem.parents[right] = left
	if problem.ranks[left] == problem.ranks[right] {
		problem.ranks[left]++
	}
}

func isDatatypeConstructorNode(node datatypeNode) bool {
	return node.kind == 1 || node.kind == 2 || node.kind == 4 || node.kind == 6 || node.kind == 8
}

func (problem *datatypeProblem) solve() (checkOutcome, bool) {
	if problem.unsat {
		return checkOutcome{status: checkUnsat}, true
	}
	for {
		changed := false
		if problem.materializeMixedUpdates() {
			changed = true
		}
		for selector, selectorNode := range problem.nodes {
			if selectorNode.kind != 3 && selectorNode.kind != 5 && selectorNode.kind != 7 && selectorNode.kind != 9 {
				continue
			}
			targetRoot := problem.find(selectorNode.child)
			for application, applicationNode := range problem.nodes {
				selected := -1
				if selectorNode.kind == 3 && applicationNode.kind == 2 {
					selected = applicationNode.child
				} else if selectorNode.kind == 5 && applicationNode.kind == 4 {
					selected = applicationNode.child
					if selectorNode.field == 1 {
						selected = applicationNode.second
					}
				} else if selectorNode.kind == 7 && applicationNode.kind == 6 && selectorNode.field < applicationNode.children.len() {
					selected = applicationNode.children.at(selectorNode.field)
				} else if selectorNode.kind == 9 && applicationNode.kind == 8 {
					selected, _ = applicationNode.mixedRecursiveChild(selectorNode.field)
				}
				if selected >= 0 && applicationNode.id == selectorNode.id && problem.find(application) == targetRoot && problem.find(selector) != problem.find(selected) {
					problem.union(selector, selected)
					changed = true
					break
				}
			}
		}
		for left := 0; left < len(problem.nodes); left++ {
			if problem.nodes[left].kind != 2 && problem.nodes[left].kind != 4 && problem.nodes[left].kind != 6 && problem.nodes[left].kind != 8 {
				continue
			}
			for right := left + 1; right < len(problem.nodes); right++ {
				sameChildren := problem.find(problem.nodes[left].child) == problem.find(problem.nodes[right].child)
				if problem.nodes[left].kind == 4 {
					sameChildren = sameChildren && problem.find(problem.nodes[left].second) == problem.find(problem.nodes[right].second)
				} else if problem.nodes[left].kind == 6 {
					sameChildren = problem.nodes[left].children.len() == problem.nodes[right].children.len()
					if sameChildren {
						for field := 0; field < problem.nodes[left].children.len(); field++ {
							if problem.find(problem.nodes[left].children.at(field)) != problem.find(problem.nodes[right].children.at(field)) {
								sameChildren = false
								break
							}
						}
					}
				} else if problem.nodes[left].kind == 8 {
					sameChildren = sameMixedDatatypeFields(problem.nodes[left].mixedSpecs, problem.nodes[right].mixedSpecs, problem.nodes[left].mixedValues, problem.nodes[right].mixedValues)
					if sameChildren {
						for field := 0; field < problem.nodes[left].mixedChildren.len(); field++ {
							if problem.find(problem.nodes[left].mixedChildren.at(field)) != problem.find(problem.nodes[right].mixedChildren.at(field)) {
								sameChildren = false
								break
							}
						}
					}
				}
				if problem.nodes[right].kind == problem.nodes[left].kind && problem.nodes[left].datatypeID == problem.nodes[right].datatypeID && problem.nodes[left].constructorCount == problem.nodes[right].constructorCount && problem.nodes[left].id == problem.nodes[right].id && sameChildren && problem.find(left) != problem.find(right) {
					problem.union(left, right)
					changed = true
				}
			}
		}
		if !changed || problem.unsat {
			break
		}
	}
	problem.propagateMixedConstructorFields()
	if problem.unsat || problem.hasRecursiveCycle() {
		return checkOutcome{status: checkUnsat}, true
	}
	for _, pair := range problem.disequalities {
		if problem.find(pair.left) == problem.find(pair.right) {
			return checkOutcome{status: checkUnsat}, true
		}
	}
	var inlineAssignment [8]int
	var assignment []int
	if len(problem.nodes) <= len(inlineAssignment) {
		assignment = inlineAssignment[:len(problem.nodes)]
	} else {
		assignment = make([]int, len(problem.nodes))
	}
	for index := range assignment {
		assignment[index] = -1
	}
	for index, node := range problem.nodes {
		if isDatatypeConstructorNode(node) {
			root := problem.find(index)
			if assignment[root] >= 0 && assignment[root] != node.id {
				return checkOutcome{status: checkUnsat}, true
			}
			assignment[root] = node.id
		}
	}
	for _, tag := range problem.tags {
		root := problem.find(tag.node)
		if !tag.negated {
			if assignment[root] >= 0 && assignment[root] != tag.constructor {
				return checkOutcome{status: checkUnsat}, true
			}
			assignment[root] = tag.constructor
		}
	}
	var inlineRoots [8]int
	roots := inlineRoots[:0]
	if len(problem.nodes) > cap(inlineRoots) {
		roots = make([]int, 0, len(problem.nodes))
	}
	for index := range problem.nodes {
		root := problem.find(index)
		if root == index && (problem.nodes[index].kind == 0 || problem.nodes[index].kind == 3 || problem.nodes[index].kind == 5 || problem.nodes[index].kind == 7 || problem.nodes[index].kind == 9) {
			roots = append(roots, root)
		}
	}
	scalarUnknown := checkOutcome{}
	scalarUnknownSeen := false
	if !problem.colorSatisfyingScalars(roots, 0, assignment, &scalarUnknown, &scalarUnknownSeen) {
		if scalarUnknownSeen {
			return scalarUnknown, true
		}
		return checkOutcome{status: checkUnsat}, true
	}
	model := &problem.model
	for index, node := range problem.nodes {
		if node.kind != 0 {
			continue
		}
		var inlineVisiting [8]bool
		var visiting []bool
		if len(problem.nodes) <= len(inlineVisiting) {
			visiting = inlineVisiting[:len(problem.nodes)]
		} else {
			visiting = make([]bool, len(problem.nodes))
		}
		value, ok := problem.valueForRoot(problem.find(index), assignment, visiting, model)
		if !ok {
			return checkOutcome{status: checkUnknown, reason: UnsupportedTheory{Name: "recursive datatype model construction"}}, true
		}
		model.set(node.datatypeID, node.id, value)
	}
	return checkOutcome{status: checkSat, booleans: problem.scalarOutcome.booleans, integers: problem.scalarOutcome.integers, reals: problem.scalarOutcome.reals, bitVectors: problem.scalarOutcome.bitVectors, datatypes: model}, true
}

func (problem *datatypeProblem) materializeMixedUpdates() bool {
	changed := false
	updateCount := len(problem.nodes)
	for update := 0; update < updateCount; update++ {
		updateNode := problem.nodes[update]
		if updateNode.kind != 10 {
			continue
		}
		targetRoot := problem.find(updateNode.child)
		materialized := false
		for application := 0; application < len(problem.nodes); application++ {
			applicationNode := problem.nodes[application]
			if !isDatatypeConstructorNode(applicationNode) || problem.find(application) != targetRoot {
				continue
			}
			if applicationNode.id != updateNode.id {
				if problem.find(update) != targetRoot {
					problem.union(update, updateNode.child)
					changed = true
				}
				materialized = true
				break
			}
			if applicationNode.kind != 8 || applicationNode.mixedSpecs.Len() != updateNode.mixedSpecs.Len() {
				problem.unsat = true
				return true
			}
			values := replaceMixedDatatypeTerm(applicationNode.mixedValues, updateNode.field, updateNode.mixedReplacement)
			rebuilt, ok := problem.term(datatypeMixedApplication[DatatypeSort]{
				datatypeID: updateNode.datatypeID, constructorCount: updateNode.constructorCount,
				constructorID: updateNode.id, name: applicationNode.name, specs: updateNode.mixedSpecs, values: values,
			})
			if !ok {
				problem.unsat = true
				return true
			}
			if problem.find(update) != problem.find(rebuilt) {
				problem.union(update, rebuilt)
				changed = true
			}
			materialized = true
			break
		}
		if materialized {
			continue
		}
		for _, tag := range problem.tags {
			if tag.negated || problem.find(tag.node) != targetRoot {
				continue
			}
			if tag.constructor != updateNode.id {
				if problem.find(update) != targetRoot {
					problem.union(update, updateNode.child)
					changed = true
				}
				break
			}
			if tag.mixedSpecs.Len() == 0 {
				continue
			}
			values := problem.syntheticMixedValues(targetRoot, updateNode.datatypeID, updateNode.constructorCount, tag.mixedSpecs)
			application, ok := problem.term(datatypeMixedApplication[DatatypeSort]{
				datatypeID: updateNode.datatypeID, constructorCount: updateNode.constructorCount,
				constructorID: updateNode.id, name: tag.name, specs: tag.mixedSpecs, values: values,
			})
			if !ok {
				problem.unsat = true
				return true
			}
			if problem.find(tag.node) != problem.find(application) {
				problem.union(tag.node, application)
				changed = true
			}
			break
		}
	}
	return changed
}

func (problem *datatypeProblem) syntheticMixedValues(root, datatypeID, constructorCount int, specs MixedDatatypeFieldSpecs) MixedDatatypeTermValues {
	var values MixedDatatypeTermValues
	for field := 0; field < specs.Len(); field++ {
		spec := specs.At(field)
		value := MixedDatatypeTermValue{
			Kind: spec.Kind, Width: spec.Width, DatatypeID: spec.DatatypeID,
			ConstructorCount: spec.ConstructorCount,
		}
		if spec.Kind == mixedDatatypeFieldSelf || spec.Kind == mixedDatatypeFieldReference {
			targetDatatype, targetConstructors := datatypeID, constructorCount
			if spec.Kind == mixedDatatypeFieldReference {
				targetDatatype, targetConstructors = spec.DatatypeID, spec.ConstructorCount
			}
			value.Term = DatatypeConstructor(targetDatatype, targetConstructors, 0, "@datatype-child-"+strconv.Itoa(root)+"-"+strconv.Itoa(field))
		} else {
			value.Term = mixedSyntheticScalar(root, field, spec)
		}
		values.append(value)
	}
	return values
}

func (problem *datatypeProblem) propagateMixedConstructorFields() {
	for left := 0; left < len(problem.nodes); left++ {
		leftNode := problem.nodes[left]
		if leftNode.kind != 8 {
			continue
		}
		for right := left + 1; right < len(problem.nodes); right++ {
			rightNode := problem.nodes[right]
			if rightNode.kind != 8 || problem.find(left) != problem.find(right) {
				continue
			}
			if leftNode.id != rightNode.id || leftNode.mixedSpecs.Len() != rightNode.mixedSpecs.Len() {
				problem.unsat = true
				return
			}
			leftSelf, rightSelf := 0, 0
			for field := 0; field < leftNode.mixedSpecs.Len(); field++ {
				leftSpec, rightSpec := leftNode.mixedSpecs.At(field), rightNode.mixedSpecs.At(field)
				if leftSpec.Kind != rightSpec.Kind || leftSpec.Width != rightSpec.Width {
					problem.unsat = true
					return
				}
				if leftSpec.Kind == mixedDatatypeFieldSelf || leftSpec.Kind == mixedDatatypeFieldReference {
					problem.union(leftNode.mixedChildren.at(leftSelf), rightNode.mixedChildren.at(rightSelf))
					leftSelf++
					rightSelf++
					continue
				}
				problem.mixedEqualities = append(problem.mixedEqualities, Equal{Left: leftNode.mixedValues.At(field).Term, Right: rightNode.mixedValues.At(field).Term})
			}
		}
	}
}

func (problem *datatypeProblem) solveMixedScalarConstraints() (checkOutcome, bool) {
	assertions := problem.mixedEqualities[:0]
	for _, assertion := range problem.mixedEqualities {
		if !mixedScalarTautology(assertion) {
			assertions = append(assertions, assertion)
		}
	}
	for _, assertion := range problem.mixedAssertions {
		rewritten, ok := problem.rewriteMixedScalarAssertion(assertion)
		if !ok {
			return checkOutcome{}, false
		}
		if !mixedScalarTautology(rewritten) {
			assertions = append(assertions, rewritten)
		}
	}
	// Retain scalar symbols that occur only as constructor fields so exact
	// mixed model extraction receives the same total model as Z3.
	for _, node := range problem.nodes {
		if node.kind != 8 {
			continue
		}
		for field := 0; field < node.mixedSpecs.Len(); field++ {
			if node.mixedSpecs.At(field).Kind == mixedDatatypeFieldSelf || node.mixedSpecs.At(field).Kind == mixedDatatypeFieldReference {
				continue
			}
			term := node.mixedValues.At(field).Term
			if mixedScalarTermNeedsModel(node.mixedSpecs.At(field), term) {
				assertions = append(assertions, Equal{Left: term, Right: term})
			}
		}
	}
	if len(assertions) == 0 {
		problem.scalarOutcome = checkOutcome{status: checkSat}
		return problem.scalarOutcome, true
	}
	var groups [4][]Term[BoolSort]
	for _, assertion := range assertions {
		group := 0
		if containsIntegerTheory(assertion) {
			group = 1
		}
		if containsRealTheory(assertion) {
			group = 2
		}
		if containsBitVectorTheory(assertion) {
			group = 3
		}
		groups[group] = append(groups[group], assertion)
	}
	combined := checkOutcome{status: checkSat}
	for _, group := range groups {
		if len(group) == 0 {
			continue
		}
		inner := engine{assertions: group}
		outcome := inner.solveAdditional(nil)
		if outcome.status != checkSat {
			problem.scalarOutcome = outcome
			return outcome, true
		}
		combined.booleans.merge(outcome.booleans)
		combined.integers.merge(outcome.integers)
		combined.reals.merge(outcome.reals)
		combined.bitVectors.merge(outcome.bitVectors)
	}
	problem.scalarOutcome = combined
	return combined, true
}

func mixedScalarTautology(assertion Term[BoolSort]) bool {
	equality, ok := assertion.(Equal)
	return ok && reflect.DeepEqual(equality.Left, equality.Right)
}

func mixedScalarTermNeedsModel(spec MixedDatatypeFieldSpec, term any) bool {
	switch spec.Kind {
	case mixedDatatypeFieldBool:
		_, ok := evaluateBool(term.(Term[BoolSort]), booleanModel{}, integerModel{}, rationalModel{})
		return !ok
	case mixedDatatypeFieldInt:
		_, ok := evaluateIntegerWithBitVectors(term.(Term[IntSort]), booleanModel{}, integerModel{}, rationalModel{}, bitVectorModel{})
		return !ok
	case mixedDatatypeFieldReal:
		_, ok := evaluateReal(term.(Term[RealSort]), booleanModel{}, integerModel{}, rationalModel{})
		return !ok
	case mixedDatatypeFieldBitVec:
		_, ok := evaluateBitVector(term, bitVectorModel{}, integerModel{})
		return !ok
	default:
		return false
	}
}

func (problem *datatypeProblem) rewriteMixedScalarAssertion(assertion Term[BoolSort]) (Term[BoolSort], bool) {
	switch value := assertion.(type) {
	case Equal:
		left, leftOK := problem.rewriteMixedScalarTerm(value.Left)
		right, rightOK := problem.rewriteMixedScalarTerm(value.Right)
		if !leftOK || !rightOK {
			return nil, false
		}
		return Equal{Left: left, Right: right}, true
	case Not:
		inner, ok := problem.rewriteMixedScalarAssertion(value.Value)
		if !ok {
			return nil, false
		}
		return Not{Value: inner}, true
	default:
		return nil, false
	}
}

func (problem *datatypeProblem) rewriteMixedScalarTerm(term any) (any, bool) {
	switch value := term.(type) {
	case datatypeMixedSelector[BoolSort]:
		return problem.mixedSelectedScalar(value.datatypeID, value.constructorCount, value.constructorID, value.field, value.fieldKind, value.width, value.value)
	case datatypeMixedSelector[IntSort]:
		return problem.mixedSelectedScalar(value.datatypeID, value.constructorCount, value.constructorID, value.field, value.fieldKind, value.width, value.value)
	case datatypeMixedSelector[RealSort]:
		return problem.mixedSelectedScalar(value.datatypeID, value.constructorCount, value.constructorID, value.field, value.fieldKind, value.width, value.value)
	case datatypeMixedSelector[BitVecSort]:
		return problem.mixedSelectedScalar(value.datatypeID, value.constructorCount, value.constructorID, value.field, value.fieldKind, value.width, value.value)
	case If[IntSort]:
		condition, conditionOK := problem.rewriteDatatypeCondition(value.Condition)
		if boolean, known := condition.(Bool); known {
			if boolean.Value {
				then, thenOK := problem.rewriteMixedScalarTerm(value.Then)
				return then, conditionOK && thenOK
			}
			otherwise, otherwiseOK := problem.rewriteMixedScalarTerm(value.Else)
			return otherwise, conditionOK && otherwiseOK
		}
		then, thenOK := problem.rewriteMixedScalarTerm(value.Then)
		otherwise, otherwiseOK := problem.rewriteMixedScalarTerm(value.Else)
		thenTerm, thenTypeOK := then.(Term[IntSort])
		otherwiseTerm, otherwiseTypeOK := otherwise.(Term[IntSort])
		return If[IntSort]{Condition: condition, Then: thenTerm, Else: otherwiseTerm}, conditionOK && thenOK && otherwiseOK && thenTypeOK && otherwiseTypeOK
	case If[RealSort]:
		condition, conditionOK := problem.rewriteDatatypeCondition(value.Condition)
		if boolean, known := condition.(Bool); known {
			if boolean.Value {
				then, thenOK := problem.rewriteMixedScalarTerm(value.Then)
				return then, conditionOK && thenOK
			}
			otherwise, otherwiseOK := problem.rewriteMixedScalarTerm(value.Else)
			return otherwise, conditionOK && otherwiseOK
		}
		then, thenOK := problem.rewriteMixedScalarTerm(value.Then)
		otherwise, otherwiseOK := problem.rewriteMixedScalarTerm(value.Else)
		thenTerm, thenTypeOK := then.(Term[RealSort])
		otherwiseTerm, otherwiseTypeOK := otherwise.(Term[RealSort])
		return If[RealSort]{Condition: condition, Then: thenTerm, Else: otherwiseTerm}, conditionOK && thenOK && otherwiseOK && thenTypeOK && otherwiseTypeOK
	case If[BoolSort]:
		condition, conditionOK := problem.rewriteDatatypeCondition(value.Condition)
		if boolean, known := condition.(Bool); known {
			if boolean.Value {
				then, thenOK := problem.rewriteMixedScalarTerm(value.Then)
				return then, conditionOK && thenOK
			}
			otherwise, otherwiseOK := problem.rewriteMixedScalarTerm(value.Else)
			return otherwise, conditionOK && otherwiseOK
		}
		then, thenOK := problem.rewriteMixedScalarTerm(value.Then)
		otherwise, otherwiseOK := problem.rewriteMixedScalarTerm(value.Else)
		thenTerm, thenTypeOK := then.(Term[BoolSort])
		otherwiseTerm, otherwiseTypeOK := otherwise.(Term[BoolSort])
		return If[BoolSort]{Condition: condition, Then: thenTerm, Else: otherwiseTerm}, conditionOK && thenOK && otherwiseOK && thenTypeOK && otherwiseTypeOK
	default:
		return term, true
	}
}

func (problem *datatypeProblem) rewriteDatatypeCondition(term Term[BoolSort]) (Term[BoolSort], bool) {
	switch value := term.(type) {
	case datatypeRecognizer:
		return problem.resolveDatatypeRecognizer(value.value, value.constructorID)
	case datatypeRecursiveRecognizer:
		return problem.resolveDatatypeRecognizer(value.value, value.constructorID)
	case datatypeBinaryRecursiveRecognizer:
		return problem.resolveDatatypeRecognizer(value.value, value.constructorID)
	case datatypeNaryRecursiveRecognizer:
		return problem.resolveDatatypeRecognizer(value.value, value.constructorID)
	case datatypeMixedRecognizer:
		return problem.resolveDatatypeRecognizer(value.value, value.constructorID)
	case Not:
		inner, ok := problem.rewriteDatatypeCondition(value.Value)
		return Not{Value: inner}, ok
	default:
		return term, true
	}
}

func (problem *datatypeProblem) resolveDatatypeRecognizer(target any, constructorID int) (Term[BoolSort], bool) {
	node, ok := problem.term(target)
	if !ok {
		return nil, false
	}
	root := problem.find(node)
	for index, candidate := range problem.nodes {
		if problem.find(index) == root && isDatatypeConstructorNode(candidate) {
			return Bool{Value: candidate.id == constructorID}, true
		}
	}
	if problem.assignment != nil && problem.assignment[root] >= 0 {
		return Bool{Value: problem.assignment[root] == constructorID}, true
	}
	return nil, false
}

func (problem *datatypeProblem) mixedSelectedScalar(datatypeID, constructorCount, constructorID, field, kind, width int, target any) (any, bool) {
	node, ok := problem.term(target)
	if !ok {
		return nil, false
	}
	root := problem.find(node)
	for index, application := range problem.nodes {
		if application.kind != 8 || application.datatypeID != datatypeID || application.constructorCount != constructorCount || application.id != constructorID || problem.find(index) != root || field < 0 || field >= application.mixedSpecs.Len() {
			continue
		}
		spec := application.mixedSpecs.At(field)
		if spec.Kind != kind || spec.Width != width || kind == mixedDatatypeFieldSelf {
			return nil, false
		}
		return application.mixedValues.At(field).Term, true
	}
	tagGroups := [2][]datatypeTagConstraint{problem.tags, problem.matchTags}
	for _, tags := range tagGroups {
		for _, tag := range tags {
			if tag.negated || tag.constructor != constructorID || tag.mixedSpecs.Len() == 0 || problem.find(tag.node) != root || field < 0 || field >= tag.mixedSpecs.Len() {
				continue
			}
			spec := tag.mixedSpecs.At(field)
			if spec.Kind != kind || spec.Width != width || kind == mixedDatatypeFieldSelf {
				return nil, false
			}
			return mixedSyntheticScalar(root, field, spec), true
		}
	}
	return nil, false
}

func mixedSyntheticScalar(root, field int, spec MixedDatatypeFieldSpec) any {
	id := -int(^uint(0)>>1) + root*1024 + field
	name := "@datatype-field-" + strconv.Itoa(root) + "-" + strconv.Itoa(field)
	switch spec.Kind {
	case mixedDatatypeFieldBool:
		return BoolSymbol{ID: id, Name: name}
	case mixedDatatypeFieldInt:
		return IntSymbol{ID: id, Name: name}
	case mixedDatatypeFieldReal:
		return RealSymbol{ID: id, Name: name}
	case mixedDatatypeFieldBitVec:
		return BitVecConst(spec.Width, id, name)
	default:
		return nil
	}
}

func (node datatypeNode) mixedRecursiveChild(field int) (int, bool) {
	if field < 0 || field >= node.mixedSpecs.Len() || node.mixedSpecs.At(field).Kind != mixedDatatypeFieldSelf && node.mixedSpecs.At(field).Kind != mixedDatatypeFieldReference {
		return -1, false
	}
	self := 0
	for index := 0; index < field; index++ {
		if node.mixedSpecs.At(index).Kind == mixedDatatypeFieldSelf || node.mixedSpecs.At(index).Kind == mixedDatatypeFieldReference {
			self++
		}
	}
	if self >= node.mixedChildren.len() {
		return -1, false
	}
	return node.mixedChildren.at(self), true
}

func (problem *datatypeProblem) valueForRoot(root int, assignment []int, visiting []bool, model *datatypeModel) (DatatypeValue, bool) {
	root = problem.find(root)
	if visiting[root] {
		return DatatypeValue{}, false
	}
	visiting[root] = true
	defer func() { visiting[root] = false }()
	for index, node := range problem.nodes {
		if node.kind != 2 && node.kind != 4 && node.kind != 6 && node.kind != 8 || problem.find(index) != root {
			continue
		}
		if node.kind == 6 {
			children := model.retainDatatypeChildren(node.children.len())
			for field := 0; field < node.children.len(); field++ {
				childNode := node.children.at(field)
				child, ok := problem.valueForRoot(problem.find(childNode), assignment, visiting, model)
				if !ok {
					return DatatypeValue{}, false
				}
				children.set(field, child)
			}
			return DatatypeValue{DatatypeID: node.datatypeID, ConstructorCount: node.constructorCount, ConstructorID: node.id, ConstructorName: node.name, Children: children}, true
		}
		if node.kind == 8 {
			fields := model.retainDatatypeFields(node.mixedSpecs.Len())
			self := 0
			for field := 0; field < node.mixedSpecs.Len(); field++ {
				spec, argument := node.mixedSpecs.At(field), node.mixedValues.At(field)
				modelField := DatatypeFieldValue{Kind: spec.Kind, Width: spec.Width}
				var ok bool
				switch spec.Kind {
				case mixedDatatypeFieldBool:
					modelField.Boolean, ok = evaluateBool(argument.Term.(Term[BoolSort]), problem.scalarOutcome.booleans, problem.scalarOutcome.integers, problem.scalarOutcome.reals)
					if !ok {
						modelField.Boolean, ok = false, true
					}
				case mixedDatatypeFieldInt:
					modelField.Integer, ok = evaluateIntegerWithBitVectors(argument.Term.(Term[IntSort]), problem.scalarOutcome.booleans, problem.scalarOutcome.integers, problem.scalarOutcome.reals, problem.scalarOutcome.bitVectors)
					if !ok {
						modelField.Integer, ok = NewIntegerValue(0), true
					}
				case mixedDatatypeFieldReal:
					modelField.Real, ok = evaluateReal(argument.Term.(Term[RealSort]), problem.scalarOutcome.booleans, problem.scalarOutcome.integers, problem.scalarOutcome.reals)
					if !ok {
						modelField.Real, ok = NewRational(0, 1), true
					}
				case mixedDatatypeFieldBitVec:
					modelField.BitVector, ok = evaluateBitVector(argument.Term, problem.scalarOutcome.bitVectors, problem.scalarOutcome.integers)
					if !ok {
						modelField.BitVector, ok = NewBitVectorUint64(spec.Width, 0), true
					}
				case mixedDatatypeFieldSelf, mixedDatatypeFieldReference:
					child, childOK := problem.valueForRoot(problem.find(node.mixedChildren.at(self)), assignment, visiting, model)
					self++
					if childOK {
						modelField.Datatype = model.retainChild(child)
					}
					ok = childOK
				}
				if !ok {
					return DatatypeValue{}, false
				}
				fields.set(field, modelField)
			}
			return DatatypeValue{DatatypeID: node.datatypeID, ConstructorCount: node.constructorCount, ConstructorID: node.id, ConstructorName: node.name, Fields: fields}, true
		}
		first, ok := problem.valueForRoot(problem.find(node.child), assignment, visiting, model)
		if !ok {
			return DatatypeValue{}, false
		}
		value := DatatypeValue{DatatypeID: node.datatypeID, ConstructorCount: node.constructorCount, ConstructorID: node.id, ConstructorName: node.name, Child: model.retainChild(first)}
		if node.kind == 4 {
			second, secondOK := problem.valueForRoot(problem.find(node.second), assignment, visiting, model)
			if !secondOK {
				return DatatypeValue{}, false
			}
			value.SecondChild = model.retainChild(second)
		}
		return value, true
	}
	node := problem.nodes[root]
	constructorID := assignment[root]
	if constructorID < 0 {
		return DatatypeValue{}, false
	}
	value := DatatypeValue{DatatypeID: node.datatypeID, ConstructorCount: node.constructorCount, ConstructorID: constructorID, ConstructorName: problem.constructorName(node.datatypeID, node.constructorCount, constructorID)}
	if specs, mixed := problem.mixedRecursiveConstructorSpecs(root, constructorID); mixed {
		fields := model.retainDatatypeFields(specs.Len())
		for field := 0; field < specs.Len(); field++ {
			spec := specs.At(field)
			modelField := DatatypeFieldValue{Kind: spec.Kind, Width: spec.Width}
			synthetic := mixedSyntheticScalar(root, field, spec)
			switch spec.Kind {
			case mixedDatatypeFieldBool:
				modelField.Boolean, _ = evaluateBool(synthetic.(Term[BoolSort]), problem.scalarOutcome.booleans, problem.scalarOutcome.integers, problem.scalarOutcome.reals)
			case mixedDatatypeFieldInt:
				if evaluated, ok := evaluateIntegerWithBitVectors(synthetic.(Term[IntSort]), problem.scalarOutcome.booleans, problem.scalarOutcome.integers, problem.scalarOutcome.reals, problem.scalarOutcome.bitVectors); ok {
					modelField.Integer = evaluated
				} else {
					modelField.Integer = NewIntegerValue(0)
				}
			case mixedDatatypeFieldReal:
				modelField.Real, _ = evaluateReal(synthetic.(Term[RealSort]), problem.scalarOutcome.booleans, problem.scalarOutcome.integers, problem.scalarOutcome.reals)
			case mixedDatatypeFieldBitVec:
				if evaluated, ok := evaluateBitVector(synthetic, problem.scalarOutcome.bitVectors, problem.scalarOutcome.integers); ok {
					modelField.BitVector = evaluated
				} else {
					modelField.BitVector = NewBitVectorUint64(spec.Width, 0)
				}
			case mixedDatatypeFieldSelf, mixedDatatypeFieldReference:
				targetDatatype, targetConstructors := node.datatypeID, node.constructorCount
				if spec.Kind == mixedDatatypeFieldReference {
					targetDatatype, targetConstructors = spec.DatatypeID, spec.ConstructorCount
				}
				base := problem.baseConstructor(targetDatatype, targetConstructors)
				if base < 0 {
					return DatatypeValue{}, false
				}
				child := DatatypeValue{DatatypeID: targetDatatype, ConstructorCount: targetConstructors, ConstructorID: base, ConstructorName: problem.constructorName(targetDatatype, targetConstructors, base)}
				modelField.Datatype = model.retainChild(child)
			}
			fields.set(field, modelField)
		}
		value.Fields = fields
		return value, true
	}
	if arity := problem.recursiveConstructorArity(root, constructorID); arity > 0 {
		base := problem.baseConstructor(node.datatypeID, node.constructorCount)
		if base < 0 {
			return DatatypeValue{}, false
		}
		child := DatatypeValue{DatatypeID: node.datatypeID, ConstructorCount: node.constructorCount, ConstructorID: base, ConstructorName: problem.constructorName(node.datatypeID, node.constructorCount, base)}
		if problem.naryRecursiveConstructor(root, constructorID) {
			children := make([]DatatypeValue, arity)
			for field := range children {
				children[field] = child
			}
			value.Children = newDatatypeChildren(children)
		} else if arity <= 2 {
			value.Child = model.retainChild(child)
		}
		if !problem.naryRecursiveConstructor(root, constructorID) && arity == 2 {
			value.SecondChild = model.retainChild(child)
		}
	}
	return value, true
}

func (problem *datatypeProblem) mixedRecursiveConstructorSpecs(root, constructor int) (MixedDatatypeFieldSpecs, bool) {
	node := problem.nodes[root]
	for _, candidate := range problem.nodes {
		if candidate.kind == 8 && candidate.datatypeID == node.datatypeID && candidate.constructorCount == node.constructorCount && candidate.id == constructor {
			return candidate.mixedSpecs, true
		}
	}
	for _, tag := range problem.tags {
		if tag.constructor == constructor && tag.mixedSpecs.Len() > 0 && problem.nodes[tag.node].datatypeID == node.datatypeID && problem.nodes[tag.node].constructorCount == node.constructorCount {
			return tag.mixedSpecs, true
		}
	}
	for _, tag := range problem.matchTags {
		if tag.constructor == constructor && tag.mixedSpecs.Len() > 0 && problem.nodes[tag.node].datatypeID == node.datatypeID && problem.nodes[tag.node].constructorCount == node.constructorCount {
			return tag.mixedSpecs, true
		}
	}
	return MixedDatatypeFieldSpecs{}, false
}

func (problem *datatypeProblem) hasRecursiveCycle() bool {
	var inlineState [8]uint8
	var state []uint8
	if len(problem.nodes) <= len(inlineState) {
		state = inlineState[:len(problem.nodes)]
	} else {
		state = make([]uint8, len(problem.nodes))
	}
	for index := range problem.nodes {
		root := problem.find(index)
		if state[root] == 0 && problem.recursiveCycleFrom(root, state) {
			return true
		}
	}
	return false
}

func (problem *datatypeProblem) recursiveCycleFrom(root int, state []uint8) bool {
	root = problem.find(root)
	if state[root] == 1 {
		return true
	}
	if state[root] == 2 {
		return false
	}
	state[root] = 1
	for index, node := range problem.nodes {
		if problem.find(index) != root || node.kind != 2 && node.kind != 4 && node.kind != 6 && node.kind != 8 {
			continue
		}
		if node.kind == 2 || node.kind == 4 {
			if problem.recursiveCycleFrom(node.child, state) {
				return true
			}
			if node.kind == 4 && problem.recursiveCycleFrom(node.second, state) {
				return true
			}
		} else if node.kind == 6 {
			for field := 0; field < node.children.len(); field++ {
				if problem.recursiveCycleFrom(node.children.at(field), state) {
					return true
				}
			}
		} else if node.kind == 8 {
			for field := 0; field < node.mixedChildren.len(); field++ {
				if problem.recursiveCycleFrom(node.mixedChildren.at(field), state) {
					return true
				}
			}
		}
	}
	state[root] = 2
	return false
}

func (problem *datatypeProblem) colorSatisfyingScalars(roots []int, position int, assignment []int, unknown *checkOutcome, unknownSeen *bool) bool {
	if position == len(roots) {
		problem.assignment = assignment
		outcome, ok := problem.solveMixedScalarConstraints()
		problem.assignment = nil
		if !ok {
			*unknown = checkOutcome{status: checkUnknown, reason: UnsupportedTheory{Name: "mixed datatype scalar exchange"}}
			*unknownSeen = true
			return false
		}
		if outcome.status == checkUnknown {
			*unknown = outcome
			*unknownSeen = true
			return false
		}
		return outcome.status == checkSat
	}
	root := roots[position]
	if assignment[root] >= 0 {
		return problem.assignmentAllowed(root, assignment[root], assignment) &&
			problem.colorSatisfyingScalars(roots, position+1, assignment, unknown, unknownSeen)
	}
	for constructor := 0; constructor < problem.nodes[root].constructorCount; constructor++ {
		if !problem.assignmentAllowed(root, constructor, assignment) {
			continue
		}
		assignment[root] = constructor
		if problem.colorSatisfyingScalars(roots, position+1, assignment, unknown, unknownSeen) {
			return true
		}
		assignment[root] = -1
	}
	return false
}

func (problem *datatypeProblem) assignmentAllowed(root, constructor int, assignment []int) bool {
	for _, tag := range problem.tags {
		if problem.find(tag.node) == root && (constructor == tag.constructor) == tag.negated {
			return false
		}
	}
	for _, pair := range problem.disequalities {
		left, right := problem.find(pair.left), problem.find(pair.right)
		if (left == root && assignment[right] == constructor || right == root && assignment[left] == constructor) && !problem.recursiveConstructor(root, constructor) {
			return false
		}
	}
	return true
}

func (problem *datatypeProblem) recursiveConstructor(root, constructor int) bool {
	return problem.recursiveConstructorArity(root, constructor) > 0
}

func (problem *datatypeProblem) recursiveConstructorArity(root, constructor int) int {
	node := problem.nodes[root]
	for _, candidate := range problem.nodes {
		if (candidate.kind == 2 || candidate.kind == 4 || candidate.kind == 6 || candidate.kind == 8) && candidate.datatypeID == node.datatypeID && candidate.constructorCount == node.constructorCount && candidate.id == constructor {
			if candidate.kind == 6 {
				return candidate.children.len()
			}
			if candidate.kind == 8 {
				return candidate.mixedChildren.len()
			}
			if candidate.kind == 4 {
				return 2
			}
			return 1
		}
	}
	for _, tag := range problem.tags {
		if tag.recursive && tag.constructor == constructor && problem.nodes[tag.node].datatypeID == node.datatypeID && problem.nodes[tag.node].constructorCount == node.constructorCount {
			return int(tag.arity)
		}
	}
	for _, tag := range problem.matchTags {
		if tag.recursive && tag.constructor == constructor && problem.nodes[tag.node].datatypeID == node.datatypeID && problem.nodes[tag.node].constructorCount == node.constructorCount {
			return int(tag.arity)
		}
	}
	return 0
}

func (problem *datatypeProblem) naryRecursiveConstructor(root, constructor int) bool {
	node := problem.nodes[root]
	for _, candidate := range problem.nodes {
		if candidate.kind == 6 && candidate.datatypeID == node.datatypeID && candidate.constructorCount == node.constructorCount && candidate.id == constructor {
			return true
		}
	}
	for _, tag := range problem.tags {
		if tag.recursive && tag.nary && tag.constructor == constructor && problem.nodes[tag.node].datatypeID == node.datatypeID && problem.nodes[tag.node].constructorCount == node.constructorCount {
			return true
		}
	}
	for _, tag := range problem.matchTags {
		if tag.recursive && tag.nary && tag.constructor == constructor && problem.nodes[tag.node].datatypeID == node.datatypeID && problem.nodes[tag.node].constructorCount == node.constructorCount {
			return true
		}
	}
	return false
}

func (problem *datatypeProblem) baseConstructor(datatypeID, constructorCount int) int {
	for constructor := 0; constructor < constructorCount; constructor++ {
		recursive := false
		for index := range problem.nodes {
			if problem.nodes[index].datatypeID == datatypeID && problem.nodes[index].constructorCount == constructorCount && problem.recursiveConstructor(index, constructor) {
				recursive = true
				break
			}
		}
		if !recursive {
			return constructor
		}
	}
	return -1
}

func (problem *datatypeProblem) constructorName(datatypeID, constructorCount, constructorID int) string {
	for _, node := range problem.nodes {
		if isDatatypeConstructorNode(node) && node.datatypeID == datatypeID && node.constructorCount == constructorCount && node.id == constructorID {
			return node.name
		}
	}
	for _, tag := range problem.tags {
		if tag.constructor == constructorID && tag.name != "" && problem.nodes[tag.node].datatypeID == datatypeID && problem.nodes[tag.node].constructorCount == constructorCount {
			return tag.name
		}
	}
	for _, tag := range problem.matchTags {
		if tag.constructor == constructorID && tag.name != "" && problem.nodes[tag.node].datatypeID == datatypeID && problem.nodes[tag.node].constructorCount == constructorCount {
			return tag.name
		}
	}
	return ""
}
