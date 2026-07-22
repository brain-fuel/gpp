// Package smtlib provides the solver-neutral SMT-LIB 2 syntax and command
// boundary used by native Go+ solvers.
package smtlib

import smt "goforge.dev/goplus/std/smt"

type Span struct {
	Start int
	End int
}

type AtomKind enum {
	SymbolAtom()
	KeywordAtom()
	NumeralAtom()
	DecimalAtom()
	StringAtom()
}

type SExpr enum {
	Atom(Kind AtomKind, Text string, At Span)
	List(Values []SExpr, At Span)
}

type Command enum {
	SetLogic(Name string, At Span)
	SetOption(Name string, Value SExpr, At Span)
	DeclareSort(Name string, Arity int, At Span)
	DeclareConst(Name string, Sort SExpr, At Span)
	DeclareFun(Name string, Domain []SExpr, Range SExpr, At Span)
	Assert(Term SExpr, At Span)
	CheckSat(At Span)
	CheckSatAssuming(Assumptions []SExpr, At Span)
	Push(Levels int, At Span)
	Pop(Levels int, At Span)
	GetModel(At Span)
	GetValue(Terms []SExpr, At Span)
	Exit(At Span)
	RawCommand(Name string, Arguments []SExpr, At Span)
}

type ParseError struct {
	Message string
	At Span
}

type ParseResult enum {
	Parsed(Commands []Command)
	Rejected(Errors []ParseError)
}

type Value enum {
	BooleanValue(Expression SExpr, Value bool)
	IntegerValue(Expression SExpr, Value int64)
	ArbitraryIntegerValue(Expression SExpr, Value smt.IntegerValue)
	RationalValue(Expression SExpr, Value smt.Rational)
	BitVectorValue(Expression SExpr, Value smt.BitVectorValue)
	DatatypeValue(Expression SExpr, Value smt.DatatypeValue)
	UnavailableValue(Expression SExpr, Reason string)
}

//goplus:derive off
type Response enum {
	Acknowledged(CommandIndex int)
	Satisfiable(Model smt.Model)
	Unsatisfiable(Proof smt.Proof)
	Unknown(Proof smt.Proof, Reason smt.UnknownReason)
	AssumptionsUnsatisfiable(Proof smt.Proof, Indices []int)
	ModelAvailable(Model smt.Model)
	ValuesAvailable(Values []Value)
}

type ExecutionError struct {
	CommandIndex int
	Message string
	At Span
}

//goplus:derive off
type ExecutionResult enum {
	Executed(Responses []Response)
	ExecutionFailed(Responses []Response, Errors []ExecutionError)
	ScriptRejected(Errors []ParseError)
}

func Parse(source string) ParseResult {
	commands, errors := parseSMTLib(source)
	if len(errors) != 0 { return Rejected(errors) }
	return Parsed(commands)
}

func Format(commands []Command) string { return formatCommands(commands) }
func FormatExpression(expression SExpr) string { return formatExpression(expression) }
func Execute(source string) ExecutionResult {
	match Parse(source) {
	case Rejected(errors): return ScriptRejected(errors)
	case Parsed(commands):
		responses, errors := executeCommands(commands)
		if len(errors) != 0 { return ExecutionFailed(responses, errors) }
		return Executed(responses)
	}
}
