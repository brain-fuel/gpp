package smt

import (
	"math/bits"
	"strings"
	"unicode/utf8"
)

type stringRegexReplace struct {
	value       Term[StringSort]
	expression  Regex[StringSort]
	replacement Term[StringSort]
	all         bool
}

func (stringRegexReplace) isTerm(StringSort) {}

// StringReplaceRegexValue replaces the shortest leftmost match in a ground
// string. The result is unknown only when the regular expression contains
// symbolic leaves that cannot be evaluated without a model.
func StringReplaceRegexValue(
	value string,
	expression Regex[StringSort],
	replacement string,
) (string, bool) {
	return evaluateStringRegexReplace(
		value, expression, replacement, stringModel{}, integerModel{}, false,
	)
}

// StringReplaceRegexAllValue replaces each shortest non-empty match in a
// ground string, scanning from left to right.
func StringReplaceRegexAllValue(
	value string,
	expression Regex[StringSort],
	replacement string,
) (string, bool) {
	return evaluateStringRegexReplace(
		value, expression, replacement, stringModel{}, integerModel{}, true,
	)
}

func makeStringRegexReplace(
	value Term[StringSort],
	expression Regex[StringSort],
	replacement Term[StringSort],
	all bool,
) Term[StringSort] {
	input, inputOK := value.(stringValue[StringSort])
	substitution, substitutionOK := replacement.(stringValue[StringSort])
	if inputOK && substitutionOK {
		result, handled := StringReplaceRegexValue(input.value, expression, substitution.value)
		if all {
			result, handled = StringReplaceRegexAllValue(input.value, expression, substitution.value)
		}
		if handled {
			return stringValue[StringSort]{value: result}
		}
	}
	return stringRegexReplace{
		value: value, expression: expression, replacement: replacement, all: all,
	}
}

func evaluateStringRegexReplace(
	value string,
	expression Regex[StringSort],
	replacement string,
	model stringModel,
	integers integerModel,
	all bool,
) (string, bool) {
	if expression.compact.count != 0 {
		if result, handled := evaluateCompactStringRegexReplace(
			value, expression.compact, replacement, all,
		); handled {
			return result, true
		}
	}
	root := regexExpressionRoot(expression)
	if root == nil {
		return "", false
	}
	input := DecodeStringCodePoints(value)
	matcher := regexMatcher{
		input: input, strings: model, integers: integers,
		memo: make(map[regexMatchKey][]bool),
	}
	if !all {
		start, end, found, known := shortestLeftmostRegexMatch(&matcher, root, 0, false)
		if !known {
			return "", false
		}
		if !found {
			return value, true
		}
		return string(input[:start]) + replacement + string(input[end:]), true
	}
	var result strings.Builder
	cursor := 0
	for cursor <= len(input) {
		start, end, found, known := shortestLeftmostRegexMatch(&matcher, root, cursor, true)
		if !known {
			return "", false
		}
		if !found {
			result.WriteString(string(input[cursor:]))
			break
		}
		result.WriteString(string(input[cursor:start]))
		result.WriteString(replacement)
		cursor = end
	}
	return result.String(), true
}

func evaluateCompactStringRegexReplace(
	value string,
	compact compactRegex,
	replacement string,
	all bool,
) (string, bool) {
	if len(value) > 62 {
		return "", false
	}
	var input [62]byte
	for index := range value {
		if value[index] >= utf8.RuneSelf {
			return "", false
		}
		input[index] = value[index]
	}
	var left [8]int8
	var right [8]int8
	var stack [8]int8
	depth := 0
	for index, operation := range compact.inline[:compact.count] {
		left[index], right[index] = -1, -1
		switch operation.kind {
		case regexComplement, regexStar, regexLoop:
			if depth < 1 {
				return "", false
			}
			left[index] = stack[depth-1]
			depth--
		case regexConcat, regexUnion, regexIntersection, regexDifference:
			if depth < 2 {
				return "", false
			}
			left[index], right[index] = stack[depth-2], stack[depth-1]
			depth -= 2
		}
		stack[depth] = int8(index)
		depth++
	}
	if depth != 1 {
		return "", false
	}
	root := int(stack[0])
	find := func(from int, nonempty bool) (int, int, bool, bool) {
		for start := from; start <= len(value); start++ {
			ends, known := compactRegexEnds(
				root, start, input, len(value), compact, left, right,
			)
			if !known {
				return 0, 0, false, false
			}
			minimum := start
			if nonempty {
				minimum++
			}
			if minimum > len(value) {
				continue
			}
			ends &= ^uint64(0) << minimum
			if ends != 0 {
				return start, bits.TrailingZeros64(ends), true, true
			}
		}
		return 0, 0, false, true
	}
	if !all {
		start, end, found, known := find(0, false)
		if !known {
			return "", false
		}
		if !found {
			return value, true
		}
		return value[:start] + replacement + value[end:], true
	}
	var result strings.Builder
	cursor := 0
	for cursor <= len(value) {
		start, end, found, known := find(cursor, true)
		if !known {
			return "", false
		}
		if !found {
			result.WriteString(value[cursor:])
			break
		}
		result.WriteString(value[cursor:start])
		result.WriteString(replacement)
		cursor = end
	}
	return result.String(), true
}

func shortestLeftmostRegexMatch(
	matcher *regexMatcher,
	root *regexNode,
	from int,
	nonempty bool,
) (int, int, bool, bool) {
	for start := from; start <= len(matcher.input); start++ {
		ends, known := matcher.ends(root, start)
		if !known {
			return 0, 0, false, false
		}
		minimum := start
		if nonempty {
			minimum++
		}
		for end := minimum; end < len(ends); end++ {
			if ends[end] {
				return start, end, true, true
			}
		}
	}
	return 0, 0, false, true
}
