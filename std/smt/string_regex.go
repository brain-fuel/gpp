package smt

import (
	"strings"
	"unicode/utf8"
)

type Regex[S any] struct {
	node         *regexNode
	compact      compactRegex
	witness      string
	witnessState uint8
}

type compactRegex struct {
	count  uint8
	inline [8]compactRegexOperation
}

type compactRegexOperation struct {
	kind          uint8
	first, second string
	minimum       int
	maximum       int
}

type regexNode struct {
	kind         uint8
	literal      Term[StringSort]
	literalValue string
	literalKnown bool
	witness      string
	witnessState uint8
	left         *regexNode
	right        *regexNode
	minimum      int
	maximum      int
}

const (
	regexNone = iota
	regexEpsilon
	regexAll
	regexAllChar
	regexLiteral
	regexRange
	regexConcat
	regexUnion
	regexIntersection
	regexDifference
	regexComplement
	regexStar
	regexLoop
)

func EmptyRegex[S any]() Regex[S] {
	return Regex[S]{compact: singleCompactRegex(compactRegexOperation{kind: regexNone}), witnessState: 1}
}

func FullRegex[S any]() Regex[S] {
	return Regex[S]{compact: singleCompactRegex(compactRegexOperation{kind: regexAll}), witnessState: 2}
}

func AllCharRegex[S any]() Regex[S] {
	return Regex[S]{compact: singleCompactRegex(compactRegexOperation{kind: regexAllChar}), witness: "a", witnessState: 2}
}

func StringToRegex(value Term[StringSort]) Regex[StringSort] {
	node := &regexNode{kind: regexLiteral, literal: value}
	if literal, ok := evaluateString(value, stringModel{}, integerModel{}); ok {
		node.literalValue, node.literalKnown = literal, true
		node.witness, node.witnessState = literal, 2
	}
	return Regex[StringSort]{node: node, witness: node.witness, witnessState: node.witnessState}
}

func StringLiteralRegex(value string) Regex[StringSort] {
	return Regex[StringSort]{
		compact: singleCompactRegex(compactRegexOperation{kind: regexLiteral, first: value}), witness: value, witnessState: 2,
	}
}

func StringRangeRegex(low, high Term[StringSort]) Regex[StringSort] {
	node := &regexNode{
		kind:  regexRange,
		left:  &regexNode{kind: regexLiteral, literal: low},
		right: &regexNode{kind: regexLiteral, literal: high},
	}
	if lowValue, lowOK := evaluateString(low, stringModel{}, integerModel{}); lowOK {
		node.left.literalValue, node.left.literalKnown = lowValue, true
	}
	if highValue, highOK := evaluateString(high, stringModel{}, integerModel{}); highOK {
		node.right.literalValue, node.right.literalKnown = highValue, true
	}
	cacheRegexRangeWitness(node)
	return Regex[StringSort]{node: node, witness: node.witness, witnessState: node.witnessState}
}

func StringValueRangeRegex(low, high string) Regex[StringSort] {
	result := Regex[StringSort]{compact: singleCompactRegex(compactRegexOperation{kind: regexRange, first: low, second: high})}
	lowCode, lowOK := compactRegexEndpoint(low)
	highCode, highOK := compactRegexEndpoint(high)
	if lowOK && highOK && lowCode <= highCode {
		result.witness, _ = EncodeStringCodePoint(int64(lowCode))
		result.witnessState = 2
	} else {
		result.witnessState = 1
	}
	return result
}

func ConcatRegex[S any](left, right Regex[S]) Regex[S] {
	return binaryRegex(regexConcat, left, right)
}

func UnionRegex[S any](left, right Regex[S]) Regex[S] {
	return binaryRegex(regexUnion, left, right)
}

func IntersectRegex[S any](left, right Regex[S]) Regex[S] {
	return binaryRegex(regexIntersection, left, right)
}

func DifferenceRegex[S any](left, right Regex[S]) Regex[S] {
	return binaryRegex(regexDifference, left, right)
}

func ComplementRegex[S any](value Regex[S]) Regex[S] {
	if compact, ok := unaryCompactRegex(value.compact, regexComplement, 0, 0); ok {
		return Regex[S]{compact: compact}
	}
	if value.node == nil {
		value.node = compactRegexNode(value.compact)
	}
	return Regex[S]{node: &regexNode{kind: regexComplement, left: value.node}}
}

func StarRegex[S any](value Regex[S]) Regex[S] {
	if compact, ok := unaryCompactRegex(value.compact, regexStar, 0, 0); ok {
		return Regex[S]{compact: compact, witnessState: 2}
	}
	return Regex[S]{node: &regexNode{kind: regexStar, left: value.node, witnessState: 2}}
}

func PlusRegex[S any](value Regex[S]) Regex[S] {
	return ConcatRegex(value, StarRegex(value))
}

func OptionalRegex[S any](value Regex[S]) Regex[S] {
	return UnionRegex(Regex[S]{
		compact: singleCompactRegex(compactRegexOperation{kind: regexEpsilon}), witnessState: 2,
	}, value)
}

func LoopRegex[S any](minimum, maximum int, value Regex[S]) Regex[S] {
	if minimum < 0 || maximum < minimum {
		panic("smt: invalid regex loop bounds")
	}
	if compact, ok := unaryCompactRegex(value.compact, regexLoop, minimum, maximum); ok {
		result := Regex[S]{compact: compact}
		if minimum == 0 {
			result.witnessState = 2
		} else if value.witnessState == 2 {
			result.witness, result.witnessState = strings.Repeat(value.witness, minimum), 2
		} else if value.witnessState == 1 {
			result.witnessState = 1
		}
		return result
	}
	if value.node == nil {
		value.node = compactRegexNode(value.compact)
	}
	node := &regexNode{kind: regexLoop, left: value.node, minimum: minimum, maximum: maximum}
	if minimum == 0 {
		node.witnessState = 2
	} else if value.node != nil && value.node.witnessState == 2 {
		node.witness, node.witnessState = strings.Repeat(value.node.witness, minimum), 2
	} else if value.node != nil && value.node.witnessState == 1 {
		node.witnessState = 1
	}
	return Regex[S]{node: node}
}

func binaryRegex[S any](kind uint8, left, right Regex[S]) Regex[S] {
	if compact, ok := binaryCompactRegex(left.compact, right.compact, kind); ok {
		result := Regex[S]{compact: compact}
		switch kind {
		case regexConcat:
			if left.witnessState == 2 && right.witnessState == 2 {
				result.witness, result.witnessState = left.witness+right.witness, 2
			} else if left.witnessState == 1 || right.witnessState == 1 {
				result.witnessState = 1
			}
		case regexUnion:
			if left.witnessState == 2 {
				result.witness, result.witnessState = left.witness, 2
			} else if right.witnessState == 2 {
				result.witness, result.witnessState = right.witness, 2
			} else if left.witnessState == 1 && right.witnessState == 1 {
				result.witnessState = 1
			}
		}
		return result
	}
	if left.node == nil {
		left.node = compactRegexNode(left.compact)
	}
	if right.node == nil {
		right.node = compactRegexNode(right.compact)
	}
	node := &regexNode{kind: kind, left: left.node, right: right.node}
	switch kind {
	case regexConcat:
		if left.node != nil && right.node != nil && left.node.witnessState == 2 && right.node.witnessState == 2 {
			node.witness, node.witnessState = left.node.witness+right.node.witness, 2
		} else if left.node != nil && right.node != nil && (left.node.witnessState == 1 || right.node.witnessState == 1) {
			node.witnessState = 1
		}
	case regexUnion:
		if left.node != nil && left.node.witnessState == 2 {
			node.witness, node.witnessState = left.node.witness, 2
		} else if right.node != nil && right.node.witnessState == 2 {
			node.witness, node.witnessState = right.node.witness, 2
		} else if left.node != nil && right.node != nil && left.node.witnessState == 1 && right.node.witnessState == 1 {
			node.witnessState = 1
		}
	}
	return Regex[S]{node: node}
}

func singleCompactRegex(operation compactRegexOperation) compactRegex {
	var result compactRegex
	result.count = 1
	result.inline[0] = operation
	return result
}

func unaryCompactRegex(value compactRegex, kind uint8, minimum, maximum int) (compactRegex, bool) {
	if value.count == 0 || int(value.count) >= len(value.inline) {
		return compactRegex{}, false
	}
	result := value
	result.inline[result.count] = compactRegexOperation{kind: kind, minimum: minimum, maximum: maximum}
	result.count++
	return result, true
}

func binaryCompactRegex(left, right compactRegex, kind uint8) (compactRegex, bool) {
	count := int(left.count) + int(right.count) + 1
	if left.count == 0 || right.count == 0 || count > len(left.inline) {
		return compactRegex{}, false
	}
	var result compactRegex
	copy(result.inline[:], left.inline[:left.count])
	copy(result.inline[left.count:], right.inline[:right.count])
	result.inline[count-1] = compactRegexOperation{kind: kind}
	result.count = uint8(count)
	return result, true
}

func compactRegexNode(compact compactRegex) *regexNode {
	var stack [8]*regexNode
	count := 0
	for _, operation := range compact.inline[:compact.count] {
		var node *regexNode
		switch operation.kind {
		case regexNone, regexEpsilon, regexAll, regexAllChar:
			node = &regexNode{kind: operation.kind}
		case regexLiteral:
			node = &regexNode{kind: regexLiteral, literalValue: operation.first, literalKnown: true}
		case regexRange:
			node = &regexNode{
				kind:  regexRange,
				left:  &regexNode{kind: regexLiteral, literalValue: operation.first, literalKnown: true},
				right: &regexNode{kind: regexLiteral, literalValue: operation.second, literalKnown: true},
			}
		case regexComplement, regexStar, regexLoop:
			if count < 1 {
				return nil
			}
			node = &regexNode{
				kind: operation.kind, left: stack[count-1], minimum: operation.minimum, maximum: operation.maximum,
			}
			count--
		default:
			if count < 2 {
				return nil
			}
			node = &regexNode{kind: operation.kind, left: stack[count-2], right: stack[count-1]}
			count -= 2
		}
		stack[count] = node
		count++
	}
	if count != 1 {
		return nil
	}
	return stack[0]
}

func compactRegexWitness(compact compactRegex) (string, bool) {
	var values [8]string
	var known [8]bool
	count := 0
	for _, operation := range compact.inline[:compact.count] {
		switch operation.kind {
		case regexNone:
			values[count], known[count] = "", false
			count++
		case regexEpsilon, regexAll, regexStar:
			values[count], known[count] = "", true
			count++
		case regexAllChar:
			values[count], known[count] = "a", true
			count++
		case regexLiteral:
			values[count], known[count] = operation.first, true
			count++
		case regexRange:
			low, lowOK := compactRegexEndpoint(operation.first)
			high, highOK := compactRegexEndpoint(operation.second)
			if lowOK && highOK && low <= high {
				values[count], known[count] = EncodeStringCodePoint(int64(low))
			}
			count++
		case regexConcat:
			if count < 2 {
				return "", false
			}
			values[count-2] = values[count-2] + values[count-1]
			known[count-2] = known[count-2] && known[count-1]
			count--
		case regexUnion:
			if count < 2 {
				return "", false
			}
			if !known[count-2] {
				values[count-2], known[count-2] = values[count-1], known[count-1]
			}
			count--
		case regexLoop:
			if count < 1 {
				return "", false
			}
			if operation.minimum == 0 {
				values[count-1], known[count-1] = "", true
			} else if known[count-1] {
				values[count-1] = strings.Repeat(values[count-1], operation.minimum)
			}
		default:
			return "", false
		}
	}
	if count != 1 {
		return "", false
	}
	return values[0], known[0]
}

func compactRegexEndpoint(value string) (rune, bool) {
	code, width := utf8.DecodeRuneInString(value)
	if width == len(value) && (code != utf8.RuneError || width > 1) {
		return code, true
	}
	codes := DecodeStringCodePoints(value)
	if len(codes) != 1 {
		return 0, false
	}
	return codes[0], true
}

func regexExpressionWitness(expression Regex[StringSort], model stringModel, integers integerModel) (string, bool) {
	if expression.witnessState != 0 {
		return expression.witness, expression.witnessState == 2
	}
	if expression.compact.count != 0 {
		return compactRegexWitness(expression.compact)
	}
	return regexWitness(expression.node, model, integers)
}

func regexExpressionRoot(expression Regex[StringSort]) *regexNode {
	if expression.node != nil {
		return expression.node
	}
	return compactRegexNode(expression.compact)
}

func cacheRegexRangeWitness(node *regexNode) {
	low, lowOK := regexEndpoint(node.left, stringModel{}, integerModel{})
	high, highOK := regexEndpoint(node.right, stringModel{}, integerModel{})
	if !lowOK || !highOK || low > high {
		node.witnessState = 1
		return
	}
	node.witness, _ = EncodeStringCodePoint(int64(low))
	node.witnessState = 2
}

func makeStringInRegex(value Term[StringSort], expression Regex[StringSort]) Term[BoolSort] {
	root := expression.node
	if root != nil {
		switch root.kind {
		case regexNone:
			return Bool{Value: false}
		case regexAll:
			return Bool{Value: true}
		}
	} else if expression.compact.count == 1 {
		switch expression.compact.inline[0].kind {
		case regexNone:
			return Bool{Value: false}
		case regexAll:
			return Bool{Value: true}
		}
	}
	text, textOK := evaluateString(value, stringModel{}, integerModel{})
	if textOK {
		if witness, ok := regexExpressionWitness(expression, stringModel{}, integerModel{}); ok && text == witness {
			return Bool{Value: true}
		}
		if root == nil {
			root = regexExpressionRoot(expression)
		}
	}
	if textOK && root != nil {
		switch root.kind {
		case regexEpsilon:
			return Bool{Value: text == ""}
		case regexLiteral:
			literal, literalOK := root.literalValue, root.literalKnown
			if !literalOK {
				literal, literalOK = evaluateString(root.literal, stringModel{}, integerModel{})
			}
			if literalOK {
				return Bool{Value: text == literal}
			}
		}
	}
	return stringInRegex{value: value, expression: expression}
}

func synthesizeStringRegex(value Term[StringSort], expression Regex[StringSort], negated bool, model *stringModel) {
	id, symbolic := stringSymbolID(value)
	if !symbolic {
		return
	}
	if _, bound := model.lookup(id); bound {
		return
	}
	var witness string
	var ok bool
	if negated {
		witness, ok = regexNonMemberWitness(expression, *model, integerModel{})
	} else {
		witness, ok = regexExpressionWitness(expression, *model, integerModel{})
	}
	if ok {
		setExistingString(model, id, witness)
	}
}

func regexWitness(node *regexNode, model stringModel, integers integerModel) (string, bool) {
	if node == nil {
		return "", false
	}
	if node.witnessState != 0 {
		return node.witness, node.witnessState == 2
	}
	switch node.kind {
	case regexNone:
		return "", false
	case regexEpsilon, regexAll, regexStar:
		return "", true
	case regexAllChar:
		return "a", true
	case regexLiteral:
		if node.literalKnown {
			return node.literalValue, true
		}
		return evaluateString(node.literal, model, integers)
	case regexRange:
		low, lowOK := regexEndpoint(node.left, model, integers)
		high, highOK := regexEndpoint(node.right, model, integers)
		if !lowOK || !highOK || low > high {
			return "", false
		}
		return EncodeStringCodePoint(int64(low))
	case regexConcat:
		left, leftOK := regexWitness(node.left, model, integers)
		right, rightOK := regexWitness(node.right, model, integers)
		return left + right, leftOK && rightOK
	case regexUnion:
		if witness, ok := regexWitness(node.left, model, integers); ok {
			return witness, true
		}
		return regexWitness(node.right, model, integers)
	case regexIntersection:
		if witness, ok := regexWitness(node.left, model, integers); ok {
			if accepted, known := regexNodeAccepts(witness, node.right, model, integers); known && accepted {
				return witness, true
			}
		}
		if witness, ok := regexWitness(node.right, model, integers); ok {
			if accepted, known := regexNodeAccepts(witness, node.left, model, integers); known && accepted {
				return witness, true
			}
		}
	case regexDifference:
		if witness, ok := regexWitness(node.left, model, integers); ok {
			if accepted, known := regexNodeAccepts(witness, node.right, model, integers); known && !accepted {
				return witness, true
			}
		}
	case regexComplement:
		for _, candidate := range regexWitnessCandidates {
			if accepted, known := regexNodeAccepts(candidate, node.left, model, integers); known && !accepted {
				return candidate, true
			}
		}
	case regexLoop:
		child, ok := regexWitness(node.left, model, integers)
		if !ok {
			if node.minimum == 0 {
				return "", true
			}
			return "", false
		}
		return strings.Repeat(child, node.minimum), true
	}
	return "", false
}

var regexWitnessCandidates = [...]string{"", "a", "b", "0", "-", "aa", "🙂"}

func regexNonMemberWitness(expression Regex[StringSort], model stringModel, integers integerModel) (string, bool) {
	if expression.node == nil && expression.compact.count == 0 {
		return "", false
	}
	for _, candidate := range regexWitnessCandidates {
		matched, known := matchesStringRegex(candidate, expression, model, integers)
		if known && !matched {
			return candidate, true
		}
	}
	return "", false
}

func regexNodeAccepts(value string, node *regexNode, model stringModel, integers integerModel) (bool, bool) {
	return matchesStringRegex(value, Regex[StringSort]{node: node}, model, integers)
}

func regexEndpoint(node *regexNode, model stringModel, integers integerModel) (rune, bool) {
	if node == nil || node.kind != regexLiteral {
		return 0, false
	}
	value, ok := node.literalValue, node.literalKnown
	if !ok {
		value, ok = evaluateString(node.literal, model, integers)
	}
	if !ok {
		return 0, false
	}
	codes := DecodeStringCodePoints(value)
	if len(codes) != 1 {
		return 0, false
	}
	return codes[0], true
}

type regexMatchKey struct {
	node  *regexNode
	start int
}

type regexMatcher struct {
	input    []rune
	strings  stringModel
	integers integerModel
	memo     map[regexMatchKey][]bool
}

func matchesStringRegex(value string, expression Regex[StringSort], strings stringModel, integers integerModel) (bool, bool) {
	root := regexExpressionRoot(expression)
	if root == nil {
		return false, false
	}
	input := DecodeStringCodePoints(value)
	matcher := regexMatcher{input: input, strings: strings, integers: integers, memo: make(map[regexMatchKey][]bool)}
	ends, ok := matcher.ends(root, 0)
	return ok && ends[len(input)], ok
}

func (matcher *regexMatcher) ends(node *regexNode, start int) ([]bool, bool) {
	key := regexMatchKey{node: node, start: start}
	if cached, ok := matcher.memo[key]; ok {
		return cached, true
	}
	result := make([]bool, len(matcher.input)+1)
	// Publish before recursion so nullable stars terminate.
	matcher.memo[key] = result
	switch node.kind {
	case regexNone:
		return result, true
	case regexEpsilon:
		result[start] = true
	case regexAll:
		for end := start; end <= len(matcher.input); end++ {
			result[end] = true
		}
	case regexAllChar:
		if start < len(matcher.input) {
			result[start+1] = true
		}
	case regexLiteral:
		literal, ok := node.literalValue, node.literalKnown
		if !ok {
			literal, ok = evaluateString(node.literal, matcher.strings, matcher.integers)
		}
		if !ok {
			return nil, false
		}
		codes := DecodeStringCodePoints(literal)
		if start+len(codes) <= len(matcher.input) && equalCodePoints(matcher.input[start:start+len(codes)], codes) {
			result[start+len(codes)] = true
		}
	case regexRange:
		low, lowValid, lowKnown := matcher.literalCode(node.left)
		high, highValid, highKnown := matcher.literalCode(node.right)
		if !lowKnown || !highKnown {
			return nil, false
		}
		if lowValid && highValid && start < len(matcher.input) && matcher.input[start] >= low && matcher.input[start] <= high {
			result[start+1] = true
		}
	case regexConcat:
		leftEnds, ok := matcher.ends(node.left, start)
		if !ok {
			return nil, false
		}
		for middle, matched := range leftEnds {
			if !matched {
				continue
			}
			rightEnds, rightOK := matcher.ends(node.right, middle)
			if !rightOK {
				return nil, false
			}
			unionRegexEnds(result, rightEnds)
		}
	case regexUnion, regexIntersection, regexDifference:
		left, leftOK := matcher.ends(node.left, start)
		right, rightOK := matcher.ends(node.right, start)
		if !leftOK || !rightOK {
			return nil, false
		}
		for end := range result {
			switch node.kind {
			case regexUnion:
				result[end] = left[end] || right[end]
			case regexIntersection:
				result[end] = left[end] && right[end]
			case regexDifference:
				result[end] = left[end] && !right[end]
			}
		}
	case regexComplement:
		child, ok := matcher.ends(node.left, start)
		if !ok {
			return nil, false
		}
		for end := start; end <= len(matcher.input); end++ {
			result[end] = !child[end]
		}
	case regexStar:
		result[start] = true
		for changed := true; changed; {
			changed = false
			for middle, reachable := range result {
				if !reachable {
					continue
				}
				next, ok := matcher.ends(node.left, middle)
				if !ok {
					return nil, false
				}
				for end, matched := range next {
					if matched && !result[end] {
						result[end], changed = true, true
					}
				}
			}
		}
	case regexLoop:
		current := make([]bool, len(result))
		current[start] = true
		for count := 0; count <= node.maximum; count++ {
			if count >= node.minimum {
				unionRegexEnds(result, current)
			}
			if count == node.maximum {
				break
			}
			next := make([]bool, len(result))
			for middle, reachable := range current {
				if !reachable {
					continue
				}
				ends, ok := matcher.ends(node.left, middle)
				if !ok {
					return nil, false
				}
				unionRegexEnds(next, ends)
			}
			current = next
		}
	default:
		return nil, false
	}
	return result, true
}

func (matcher *regexMatcher) literalCode(node *regexNode) (rune, bool, bool) {
	value, ok := node.literalValue, node.literalKnown
	if !ok {
		value, ok = evaluateString(node.literal, matcher.strings, matcher.integers)
	}
	if !ok {
		return 0, false, false
	}
	codes := DecodeStringCodePoints(value)
	if len(codes) != 1 {
		return 0, false, true
	}
	return codes[0], true, true
}

func equalCodePoints(left, right []rune) bool {
	if len(left) != len(right) {
		return false
	}
	for index := range left {
		if left[index] != right[index] {
			return false
		}
	}
	return true
}

func unionRegexEnds(target, source []bool) {
	for index, value := range source {
		target[index] = target[index] || value
	}
}

func collectRegexStringSymbols(node *regexNode, symbols *stringSymbols) {
	if node == nil {
		return
	}
	if node.literal != nil {
		collectStringSymbols(node.literal, symbols)
	}
	collectRegexStringSymbols(node.left, symbols)
	collectRegexStringSymbols(node.right, symbols)
}
