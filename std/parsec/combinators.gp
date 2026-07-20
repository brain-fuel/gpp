// Derived combinators and the lexeme layer, built on the consumed/empty
// core — sequencing, repetition, separators, operator chains, and
// whitespace handling.
package parsec

import "unicode"

// Pair carries two sequenced results.
type Pair[A any, B any] struct {
	First  A
	Second B
}

// Then sequences, keeping the right result.
func Then[A any, B any](p Parser[A], q Parser[B]) Parser[B] {
	return Bind(p, func(_ A) Parser[B] { return q })
}

// Before sequences, keeping the left result.
func Before[A any, B any](p Parser[A], q Parser[B]) Parser[A] {
	return Bind(p, func(v A) Parser[A] {
		return Map(q, func(_ B) A { return v })
	})
}

// Seq2 sequences two parsers into a Pair.
func Seq2[A any, B any](p Parser[A], q Parser[B]) Parser[Pair[A, B]] {
	return Bind(p, func(a A) Parser[Pair[A, B]] {
		return Map(q, func(b B) Pair[A, B] { return Pair[A, B]{First: a, Second: b} })
	})
}

// Many collects zero or more p. A p that succeeds without consuming
// would loop forever; that is reported as a failure naming the misuse.
func Many[T any](p Parser[T]) Parser[[]T] {
	return func(in Input) Reply[[]T] {
		var out []T
		cur := in
		consumed := false
		for {
			done := false
			var reply Reply[[]T]
			match p(cur) {
			case ConsumedOk(v, rest):
				out = append(out, v)
				cur = rest
				consumed = true
			case EmptyOk(v, rest):
				_ = v
				_ = rest
				reply = EmptyErr[[]T](errAt(cur, "Many applied to a parser that accepts empty input", nil))
				done = true
			case ConsumedErr(e):
				reply = ConsumedErr[[]T](e)
				done = true
			case EmptyErr(e):
				_ = e
				if consumed {
					reply = ConsumedOk(out, cur)
				} else {
					reply = EmptyOk(out, cur)
				}
				done = true
			}
			if done {
				return reply
			}
		}
	}
}

// Many1 collects one or more p.
func Many1[T any](p Parser[T]) Parser[[]T] {
	return Bind(p, func(v T) Parser[[]T] {
		return Map(Many(p), func(vs []T) []T {
			return append([]T{v}, vs...)
		})
	})
}

// SepBy collects zero or more p separated by sep.
func SepBy[T any, S any](p Parser[T], sep Parser[S]) Parser[[]T] {
	return Or(SepBy1(p, sep), Return[[]T](nil))
}

// SepBy1 collects one or more p separated by sep.
func SepBy1[T any, S any](p Parser[T], sep Parser[S]) Parser[[]T] {
	return Bind(p, func(v T) Parser[[]T] {
		return Map(Many(Then(sep, p)), func(vs []T) []T {
			return append([]T{v}, vs...)
		})
	})
}

// Between runs p bracketed by open and close.
func Between[O any, T any, C any](open Parser[O], p Parser[T], close Parser[C]) Parser[T] {
	return Then(open, Before(p, close))
}

// Opt runs p, yielding dflt when p fails without consuming.
func Opt[T any](p Parser[T], dflt T) Parser[T] {
	return Or(p, Return(dflt))
}

// Chainl1 parses one or more p separated by op, folding left — the
// standard left-associative operator chain.
func Chainl1[T any](p Parser[T], op Parser[func(T, T) T]) Parser[T] {
	var rest func(T) Parser[T]
	rest = func(x T) Parser[T] {
		return Or(
			Bind(op, func(f func(T, T) T) Parser[T] {
				return Bind(p, func(y T) Parser[T] {
					return rest(f(x, y))
				})
			}),
			Return(x),
		)
	}
	return Bind(p, rest)
}

// Spaces consumes any run of whitespace.
func Spaces() Parser[string] {
	return TakeWhile(unicode.IsSpace)
}

// Lexeme runs p, then consumes trailing whitespace.
func Lexeme[T any](p Parser[T]) Parser[T] {
	return Before(p, Spaces())
}

// Symbol is a Lexeme'd literal string.
func Symbol(s string) Parser[string] {
	return Lexeme(Str(s))
}

// Defer resolves a parser at parse time — the forward reference for
// recursive grammars: declare the variable, build the grammar against
// Defer(&expr), assign expr last.
func Defer[T any](p *Parser[T]) Parser[T] {
	return func(in Input) Reply[T] {
		return (*p)(in)
	}
}
