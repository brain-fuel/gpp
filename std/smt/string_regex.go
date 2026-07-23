package smt

type Regex[S any] struct {
	node *regexNode
}

type regexNode struct {
	kind    uint8
	literal Term[StringSort]
	left    *regexNode
	right   *regexNode
	minimum int
	maximum int
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
	return Regex[S]{node: &regexNode{kind: regexNone}}
}

func FullRegex[S any]() Regex[S] {
	return Regex[S]{node: &regexNode{kind: regexAll}}
}

func AllCharRegex[S any]() Regex[S] {
	return Regex[S]{node: &regexNode{kind: regexAllChar}}
}

func StringToRegex(value Term[StringSort]) Regex[StringSort] {
	return Regex[StringSort]{node: &regexNode{kind: regexLiteral, literal: value}}
}

func StringRangeRegex(low, high Term[StringSort]) Regex[StringSort] {
	return Regex[StringSort]{node: &regexNode{
		kind:  regexRange,
		left:  &regexNode{kind: regexLiteral, literal: low},
		right: &regexNode{kind: regexLiteral, literal: high},
	}}
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
	return Regex[S]{node: &regexNode{kind: regexComplement, left: value.node}}
}

func StarRegex[S any](value Regex[S]) Regex[S] {
	return Regex[S]{node: &regexNode{kind: regexStar, left: value.node}}
}

func PlusRegex[S any](value Regex[S]) Regex[S] {
	return ConcatRegex(value, StarRegex(value))
}

func OptionalRegex[S any](value Regex[S]) Regex[S] {
	return UnionRegex(Regex[S]{node: &regexNode{kind: regexEpsilon}}, value)
}

func LoopRegex[S any](minimum, maximum int, value Regex[S]) Regex[S] {
	if minimum < 0 || maximum < minimum {
		panic("smt: invalid regex loop bounds")
	}
	return Regex[S]{node: &regexNode{kind: regexLoop, left: value.node, minimum: minimum, maximum: maximum}}
}

func binaryRegex[S any](kind uint8, left, right Regex[S]) Regex[S] {
	return Regex[S]{node: &regexNode{kind: kind, left: left.node, right: right.node}}
}

func makeStringInRegex(value Term[StringSort], expression Regex[StringSort]) Term[BoolSort] {
	text, textOK := evaluateString(value, stringModel{}, integerModel{})
	if textOK && expression.node != nil {
		switch expression.node.kind {
		case regexNone:
			return Bool{Value: false}
		case regexEpsilon:
			return Bool{Value: text == ""}
		case regexAll:
			return Bool{Value: true}
		case regexLiteral:
			literal, literalOK := evaluateString(expression.node.literal, stringModel{}, integerModel{})
			if literalOK {
				return Bool{Value: text == literal}
			}
		}
	}
	return stringInRegex{value: value, expression: expression}
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
	if expression.node == nil {
		return false, false
	}
	input := DecodeStringCodePoints(value)
	matcher := regexMatcher{input: input, strings: strings, integers: integers, memo: make(map[regexMatchKey][]bool)}
	ends, ok := matcher.ends(expression.node, 0)
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
		literal, ok := evaluateString(node.literal, matcher.strings, matcher.integers)
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
	value, ok := evaluateString(node.literal, matcher.strings, matcher.integers)
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
