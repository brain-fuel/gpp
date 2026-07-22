// Package schedule provides immutable grammar-indexed calendar schedules.
package schedule

import "time"

type Grammar enum {
	StandardGrammar()
	SecondsGrammar()
}

// FieldSet[d] is a nonempty subset of a finite domain of size d.
//goplus:derive off
type FieldSet[d nat] enum {
	fieldSetValue(Mask uint64) FieldSet[d]
}

// Schedule[f] records the grammar field count: standard schedules have five
// fields and seconds-enabled schedules have six.
//goplus:derive off
type Schedule[f nat] enum {
	calendarValue(Grammar Grammar, Second FieldSet[60], Minute FieldSet[60], Hour FieldSet[24], DayOfMonth FieldSet[31], Month FieldSet[12], DayOfWeek FieldSet[7], Location *time.Location, DomWildcard bool, DowWildcard bool) Schedule[f]
	delayValue(Grammar Grammar, Delay time.Duration, Location *time.Location) Schedule[f]
}

type ParseError struct { Message string }
func (e ParseError) Error() string { return e.Message }

type ParseResult[f nat] enum {
	Parsed(Value Schedule[f])
	Rejected(Error ParseError)
}

// SomeSchedule is the finite existential grammar boundary for runtime input.
type SomeSchedule enum {
	StandardSchedule(Value Schedule[5])
	SecondsSchedule(Value Schedule[6])
}

type DynamicParse enum {
	DynamicallyParsed(Value SomeSchedule)
	DynamicRejected(Error ParseError)
}

type NextResult enum {
	NextAt(Time time.Time)
	NoNext(Reason string)
}

func ParseStandard(spec string) ParseResult[5] {
	value, err := parseCalendar(spec, false, time.Local)
	if err != nil { return Rejected(ParseError{Message: err.Error()}) }
	return Parsed(value)
}

func ParseStandardInLocation(spec string, location *time.Location) ParseResult[5] {
	value, err := parseCalendar(spec, false, location)
	if err != nil { return Rejected(ParseError{Message: err.Error()}) }
	return Parsed(value)
}

func ParseSeconds(spec string) ParseResult[6] {
	value, err := parseCalendar(spec, true, time.Local)
	if err != nil { return Rejected(ParseError{Message: err.Error()}) }
	return Parsed(value)
}

func ParseSecondsInLocation(spec string, location *time.Location) ParseResult[6] {
	value, err := parseCalendar(spec, true, location)
	if err != nil { return Rejected(ParseError{Message: err.Error()}) }
	return Parsed(value)
}

func ParseDynamic(spec string, grammar Grammar) DynamicParse {
	match grammar {
	case StandardGrammar():
		match ParseStandard(spec) { case Parsed(value): return DynamicallyParsed(StandardSchedule(value)); case Rejected(error): return DynamicRejected(error) }
	case SecondsGrammar():
		match ParseSeconds(spec) { case Parsed(value): return DynamicallyParsed(SecondsSchedule(value)); case Rejected(error): return DynamicRejected(error) }
	}
}

func NextStandard(schedule Schedule[5], after time.Time) NextResult { return nextCalendar(schedule, StandardGrammar(), after) }
func NextSeconds(schedule Schedule[6], after time.Time) NextResult { return nextCalendar(schedule, SecondsGrammar(), after) }

func newFieldSet(domain nat, mask uint64) FieldSet[domain] {
	if domain <= 0 || domain > 64 { panic("schedule: invalid field domain") }
	if mask == 0 { panic("schedule: empty field set") }
	if domain < 64 && mask >> uint(domain) != 0 { panic("schedule: field bit outside domain") }
	return fieldSetValue(mask)
}

func newCalendar(0 fields nat, grammar Grammar, second, minute, hour, dayOfMonth, month, dayOfWeek uint64, location *time.Location, domWildcard, dowWildcard bool) Schedule[fields] {
	if location == nil { panic("schedule: nil location") }
	return calendarValue(grammar, newFieldSet(60, second), newFieldSet(60, minute), newFieldSet(24, hour), newFieldSet(31, dayOfMonth), newFieldSet(12, month), newFieldSet(7, dayOfWeek), location, domWildcard, dowWildcard)
}

func newDelay(0 fields nat, grammar Grammar, delay time.Duration, location *time.Location) Schedule[fields] {
	if delay <= 0 { panic("schedule: non-positive delay") }
	if location == nil { panic("schedule: nil location") }
	return delayValue(grammar, delay, location)
}
