package smt

const (
	mixedDatatypeFieldBool = iota + 1
	mixedDatatypeFieldInt
	mixedDatatypeFieldReal
	mixedDatatypeFieldBitVec
	mixedDatatypeFieldSelf
)

type MixedDatatypeFieldSpec struct {
	Kind  int
	Width int
	Name  string
}

type MixedDatatypeFieldSpecs struct {
	Count    int
	Inline   [4]MixedDatatypeFieldSpec
	Overflow []MixedDatatypeFieldSpec
}

func (specs MixedDatatypeFieldSpecs) Len() int { return specs.Count }

func (specs MixedDatatypeFieldSpecs) At(index int) MixedDatatypeFieldSpec {
	if index < 0 || index >= specs.Count {
		panic("smt: mixed datatype field outside signature")
	}
	if specs.Overflow != nil {
		return specs.Overflow[index]
	}
	return specs.Inline[index]
}

func prependMixedDatatypeFieldSpec(kind, width int, name string, tail MixedDatatypeFieldSpecs) MixedDatatypeFieldSpecs {
	var result MixedDatatypeFieldSpecs
	result.Count = tail.Count + 1
	if result.Count <= len(result.Inline) {
		result.Inline[0] = MixedDatatypeFieldSpec{Kind: kind, Width: width, Name: name}
		for index := 0; index < tail.Count; index++ {
			result.Inline[index+1] = tail.At(index)
		}
		return result
	}
	result.Overflow = make([]MixedDatatypeFieldSpec, result.Count)
	result.Overflow[0] = MixedDatatypeFieldSpec{Kind: kind, Width: width, Name: name}
	for index := 0; index < tail.Count; index++ {
		result.Overflow[index+1] = tail.At(index)
	}
	return result
}

func validateMixedDatatypeFieldSpecs(specs MixedDatatypeFieldSpecs) {
	if specs.Len() == 0 {
		panic("smt: mixed recursive constructor requires at least one field")
	}
	for left := 0; left < specs.Len(); left++ {
		item := specs.At(left)
		if item.Kind == mixedDatatypeFieldBitVec && item.Width <= 0 {
			panic("smt: mixed datatype bit-vector field width must be positive")
		}
		for right := left + 1; right < specs.Len(); right++ {
			if item.Name == specs.At(right).Name {
				panic("smt: mixed datatype selector names must be distinct")
			}
		}
	}
}

type MixedDatatypeTermValue struct {
	Kind  int
	Width int
	Term  any
}

type MixedDatatypeTermValues struct {
	Count    int
	Inline   [4]MixedDatatypeTermValue
	Overflow []MixedDatatypeTermValue
}

// DatatypeFieldValue is one exact field in a mixed-constructor model.
// Exactly one value member is meaningful according to Kind.
type DatatypeFieldValue struct {
	Kind      int
	Width     int
	Boolean   bool
	Integer   IntegerValue
	Real      Rational
	BitVector BitVectorValue
	Datatype  *DatatypeValue
}

type DatatypeFields struct {
	Count    int
	Inline   [4]DatatypeFieldValue
	Overflow []DatatypeFieldValue
}

func (fields *DatatypeFields) Len() int {
	if fields == nil {
		return 0
	}
	return fields.Count
}

func (fields *DatatypeFields) At(index int) (DatatypeFieldValue, bool) {
	if fields == nil || index < 0 || index >= fields.Count {
		return DatatypeFieldValue{}, false
	}
	if fields.Overflow != nil {
		return fields.Overflow[index], true
	}
	return fields.Inline[index], true
}

func (fields *DatatypeFields) set(index int, value DatatypeFieldValue) {
	if fields.Overflow != nil {
		fields.Overflow[index] = value
		return
	}
	fields.Inline[index] = value
}

func (values MixedDatatypeTermValues) Len() int { return values.Count }

func (values MixedDatatypeTermValues) At(index int) MixedDatatypeTermValue {
	if index < 0 || index >= values.Count {
		panic("smt: mixed datatype argument outside signature")
	}
	if values.Overflow != nil {
		return values.Overflow[index]
	}
	return values.Inline[index]
}

func prependMixedDatatypeTerm(kind, width int, term any, tail MixedDatatypeTermValues) MixedDatatypeTermValues {
	var result MixedDatatypeTermValues
	result.Count = tail.Count + 1
	if result.Count <= len(result.Inline) {
		result.Inline[0] = MixedDatatypeTermValue{Kind: kind, Width: width, Term: term}
		for index := 0; index < tail.Count; index++ {
			result.Inline[index+1] = tail.At(index)
		}
		return result
	}
	result.Overflow = make([]MixedDatatypeTermValue, result.Count)
	result.Overflow[0] = MixedDatatypeTermValue{Kind: kind, Width: width, Term: term}
	for index := 0; index < tail.Count; index++ {
		result.Overflow[index+1] = tail.At(index)
	}
	return result
}

func validateMixedDatatypeArguments(specs MixedDatatypeFieldSpecs, values MixedDatatypeTermValues) {
	if specs.Len() != values.Len() {
		panic("smt: mixed datatype argument count does not match signature")
	}
	for index := 0; index < specs.Len(); index++ {
		spec, value := specs.At(index), values.At(index)
		if spec.Kind != value.Kind || spec.Width != value.Width {
			panic("smt: mixed datatype argument sort does not match signature")
		}
	}
}
