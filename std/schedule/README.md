# `std/schedule`

`std/schedule` is the immutable, effect-free scheduling core extracted from the
Robfig Cron rewrite. It deliberately separates five-field standard syntax from
six-field seconds syntax:

```go
result := schedule.ParseStandardInLocation("*/15 9-17 * * MON-FRI", time.UTC)
match result {
case schedule.Parsed(value):
	next := schedule.NextStandard(value, time.Now())
case schedule.Rejected(problem):
	// problem is exhaustive, structured parse failure
}
```

In Go+ source, the values are `Schedule[5]` and `Schedule[6]`; passing a
standard schedule to `NextSeconds` is a type error. Every calendar field is a
sealed nonempty `FieldSet[d]`. Runtime-selected grammars return `SomeSchedule`,
a finite existential whose match recovers the index. `NextResult` makes an
unsatisfiable eight-year search explicit instead of encoding it as a zero time.

The parser supports Robfig's lists, ranges, steps, month/day names, `?` in day
fields, descriptors, `@every`, and `TZ=`/`CRON_TZ=`. Day-of-month/day-of-week
use Robfig's OR rule. Next-time calculation checks actual wall-clock
occurrences, including missing and repeated DST times.

The package has two production consumers: `goforge.dev/cron` owns effects and
overlap behavior, while `std/workflow` attaches validated schedules to durable
workflow start planning.

The design is independently structured. Robfig Cron v3.0.1 is the pinned
differential baseline; its MIT notice is retained in the sibling Cron module.
