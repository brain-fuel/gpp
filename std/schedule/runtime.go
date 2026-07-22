package schedule

import (
	"fmt"
	"strconv"
	"strings"
	"time"
)

var monthNames = map[string]int{"jan": 1, "feb": 2, "mar": 3, "apr": 4, "may": 5, "jun": 6, "jul": 7, "aug": 8, "sep": 9, "oct": 10, "nov": 11, "dec": 12}
var weekdayNames = map[string]int{"sun": 0, "mon": 1, "tue": 2, "wed": 3, "thu": 4, "fri": 5, "sat": 6}

func parseCalendar(spec string, seconds bool, location *time.Location) (Schedule, error) {
	if location == nil {
		return nil, fmt.Errorf("schedule: nil location")
	}
	spec = strings.TrimSpace(spec)
	if strings.HasPrefix(spec, "TZ=") || strings.HasPrefix(spec, "CRON_TZ=") {
		space := strings.IndexByte(spec, ' ')
		if space < 0 {
			return nil, fmt.Errorf("schedule: timezone without expression")
		}
		assignment := spec[:space]
		name := assignment[strings.IndexByte(assignment, '=')+1:]
		loaded, err := time.LoadLocation(name)
		if err != nil {
			return nil, fmt.Errorf("schedule: timezone %q: %w", name, err)
		}
		location = loaded
		spec = strings.TrimSpace(spec[space+1:])
	}
	if strings.HasPrefix(spec, "@") {
		return parseDescriptor(spec, seconds, location)
	}
	fields := splitFields(spec)
	want := 5
	if seconds {
		want = 6
	}
	if len(fields) != want {
		return nil, fmt.Errorf("schedule: expected %d fields, got %d", want, len(fields))
	}
	at := 0
	second := uint64(1)
	if seconds {
		var err error
		second, _, err = parseField(fields[at], 0, 59, nil, false)
		if err != nil {
			return nil, fieldError("second", err)
		}
		at++
	}
	minute, _, err := parseField(fields[at], 0, 59, nil, false)
	if err != nil {
		return nil, fieldError("minute", err)
	}
	at++
	hour, _, err := parseField(fields[at], 0, 23, nil, false)
	if err != nil {
		return nil, fieldError("hour", err)
	}
	at++
	dom, domWildcard, err := parseField(fields[at], 1, 31, nil, true)
	if err != nil {
		return nil, fieldError("day-of-month", err)
	}
	at++
	month, _, err := parseField(fields[at], 1, 12, monthNames, false)
	if err != nil {
		return nil, fieldError("month", err)
	}
	at++
	dow, dowWildcard, err := parseField(fields[at], 0, 6, weekdayNames, true)
	if err != nil {
		return nil, fieldError("day-of-week", err)
	}
	if seconds {
		return newCalendar(SecondsGrammar{}, second, minute, hour, dom, month, dow, location, domWildcard, dowWildcard), nil
	}
	return newCalendar(StandardGrammar{}, second, minute, hour, dom, month, dow, location, domWildcard, dowWildcard), nil
}

func parseDescriptor(spec string, seconds bool, location *time.Location) (Schedule, error) {
	var expanded string
	switch strings.ToLower(spec) {
	case "@yearly", "@annually":
		expanded = "0 0 1 1 *"
	case "@monthly":
		expanded = "0 0 1 * *"
	case "@weekly":
		expanded = "0 0 * * 0"
	case "@daily", "@midnight":
		expanded = "0 0 * * *"
	case "@hourly":
		expanded = "0 * * * *"
	default:
		if strings.HasPrefix(strings.ToLower(spec), "@every ") {
			duration, err := time.ParseDuration(strings.TrimSpace(spec[7:]))
			if err != nil || duration <= 0 {
				return nil, fmt.Errorf("schedule: invalid @every duration")
			}
			if duration < time.Second {
				duration = time.Second
			} else {
				duration = duration.Truncate(time.Second)
			}
			if seconds {
				return newDelay(SecondsGrammar{}, duration, location), nil
			}
			return newDelay(StandardGrammar{}, duration, location), nil
		}
		return nil, fmt.Errorf("schedule: unknown descriptor %q", spec)
	}
	if seconds {
		expanded = "0 " + expanded
	}
	return parseCalendar(expanded, seconds, location)
}

func splitFields(spec string) []string {
	var out []string
	for i := 0; i < len(spec); {
		for i < len(spec) && (spec[i] == ' ' || spec[i] == '\t' || spec[i] == '\n' || spec[i] == '\r') {
			i++
		}
		if i == len(spec) {
			break
		}
		start := i
		for i < len(spec) && spec[i] != ' ' && spec[i] != '\t' && spec[i] != '\n' && spec[i] != '\r' {
			i++
		}
		out = append(out, spec[start:i])
	}
	return out
}

func parseField(text string, min, max int, names map[string]int, question bool) (uint64, bool, error) {
	wildcard := text == "*" || question && text == "?"
	if wildcard {
		return rangeMask(min, max, 1, min), true, nil
	}
	mask := uint64(0)
	for len(text) > 0 {
		part := text
		if comma := strings.IndexByte(text, ','); comma >= 0 {
			part, text = text[:comma], text[comma+1:]
		} else {
			text = ""
		}
		if part == "" {
			return 0, false, fmt.Errorf("empty list item")
		}
		step := 1
		if slash := strings.IndexByte(part, '/'); slash >= 0 {
			parsed, err := strconv.Atoi(part[slash+1:])
			if err != nil || parsed <= 0 {
				return 0, false, fmt.Errorf("invalid step")
			}
			step = parsed
			part = part[:slash]
		}
		lo, hi := min, max
		if part != "*" {
			if dash := strings.IndexByte(part, '-'); dash >= 0 {
				var err error
				lo, err = parseAtom(part[:dash], names)
				if err != nil {
					return 0, false, err
				}
				hi, err = parseAtom(part[dash+1:], names)
				if err != nil {
					return 0, false, err
				}
			} else {
				value, err := parseAtom(part, names)
				if err != nil {
					return 0, false, err
				}
				lo, hi = value, value
				if step > 1 {
					hi = max
				}
			}
		}
		if lo < min || hi > max || lo > hi {
			return 0, false, fmt.Errorf("range %d-%d outside %d-%d", lo, hi, min, max)
		}
		mask |= rangeMask(lo, hi, step, min)
	}
	if mask == 0 {
		return 0, false, fmt.Errorf("empty field")
	}
	return mask, false, nil
}
func parseAtom(text string, names map[string]int) (int, error) {
	if names != nil {
		if value, ok := namedValue(text, names); ok {
			return value, nil
		}
	}
	value, err := strconv.Atoi(text)
	if err != nil {
		return 0, fmt.Errorf("invalid value %q", text)
	}
	return value, nil
}
func namedValue(text string, names map[string]int) (int, bool) {
	if value, ok := names[text]; ok {
		return value, true
	}
	if len(text) != 3 {
		return 0, false
	}
	a, b, c := text[0]|0x20, text[1]|0x20, text[2]|0x20
	var canonical string
	switch {
	case a == 'j' && b == 'a' && c == 'n':
		canonical = "jan"
	case a == 'f' && b == 'e' && c == 'b':
		canonical = "feb"
	case a == 'm' && b == 'a' && c == 'r':
		canonical = "mar"
	case a == 'a' && b == 'p' && c == 'r':
		canonical = "apr"
	case a == 'm' && b == 'a' && c == 'y':
		canonical = "may"
	case a == 'j' && b == 'u' && c == 'n':
		canonical = "jun"
	case a == 'j' && b == 'u' && c == 'l':
		canonical = "jul"
	case a == 'a' && b == 'u' && c == 'g':
		canonical = "aug"
	case a == 's' && b == 'e' && c == 'p':
		canonical = "sep"
	case a == 'o' && b == 'c' && c == 't':
		canonical = "oct"
	case a == 'n' && b == 'o' && c == 'v':
		canonical = "nov"
	case a == 'd' && b == 'e' && c == 'c':
		canonical = "dec"
	case a == 's' && b == 'u' && c == 'n':
		canonical = "sun"
	case a == 'm' && b == 'o' && c == 'n':
		canonical = "mon"
	case a == 't' && b == 'u' && c == 'e':
		canonical = "tue"
	case a == 'w' && b == 'e' && c == 'd':
		canonical = "wed"
	case a == 't' && b == 'h' && c == 'u':
		canonical = "thu"
	case a == 'f' && b == 'r' && c == 'i':
		canonical = "fri"
	case a == 's' && b == 'a' && c == 't':
		canonical = "sat"
	default:
		return 0, false
	}
	value, ok := names[canonical]
	return value, ok
}
func rangeMask(min, max, step, base int) uint64 {
	mask := uint64(0)
	for value := min; value <= max; value += step {
		mask |= uint64(1) << uint(value-base)
	}
	return mask
}
func fieldError(name string, err error) error { return fmt.Errorf("schedule: %s: %w", name, err) }

func nextCalendar(raw Schedule, expected Grammar, after time.Time) NextResult {
	switch value := raw.(type) {
	case delayValue:
		if !GrammarEqual(value.grammar, expected) {
			return NoNext{Reason: "schedule grammar witness mismatch"}
		}
		return NextAt{Time: after.Add(value.delay).Truncate(time.Second)}
	case calendarValue:
		if !GrammarEqual(value.grammar, expected) {
			return NoNext{Reason: "schedule grammar witness mismatch"}
		}
		return nextSpec(value, after)
	default:
		return NoNext{Reason: "invalid erased schedule"}
	}
}

func nextSpec(spec calendarValue, after time.Time) NextResult {
	location := spec.location
	if location == nil {
		return NoNext{Reason: "nil location"}
	}
	local := after.In(location)
	startYear := local.Year()
	for year := startYear; year <= startYear+8; year++ {
		monthStart := time.January
		if year == local.Year() {
			monthStart = local.Month()
		}
		for month := monthStart; month <= time.December; month++ {
			if !bit(fieldMask(spec.month), int(month)-1) {
				continue
			}
			days := daysInMonth(year, month)
			dayStart := 1
			if year == local.Year() && month == local.Month() {
				dayStart = local.Day()
			}
			for day := dayStart; day <= days; day++ {
				if !dayMatches(spec, year, month, day) {
					continue
				}
				hourStart := 0
				if year == local.Year() && month == local.Month() && day == local.Day() {
					// Revisit a small wall-clock window so the second occurrence of a
					// repeated fall-back hour remains discoverable.
					hourStart = local.Hour() - 3
					if hourStart < 0 {
						hourStart = 0
					}
				}
				for hour := hourStart; hour < 24; hour++ {
					if !bit(fieldMask(spec.hour), hour) {
						continue
					}
					for minute := 0; minute < 60; minute++ {
						if !bit(fieldMask(spec.minute), minute) {
							continue
						}
						for second := 0; second < 60; second++ {
							if !bit(fieldMask(spec.second), second) {
								continue
							}
							candidate := time.Date(year, month, day, hour, minute, second, 0, location)
							found := chooseWallOccurrence(time.Time{}, candidate, year, month, day, hour, minute, second, after)
							if !found.IsZero() {
								return NextAt{Time: found}
							}
						}
					}
				}
			}
		}
	}
	return NoNext{Reason: "no occurrence within eight years"}
}
func chooseWallOccurrence(best, candidate time.Time, year int, month time.Month, day, hour, minute, second int, after time.Time) time.Time {
	for offset := -3 * time.Hour; offset <= 3*time.Hour; offset += 15 * time.Minute {
		option := candidate.Add(offset)
		y, m, d := option.In(candidate.Location()).Date()
		h, min, s := option.In(candidate.Location()).Clock()
		if y == year && m == month && d == day && h == hour && min == minute && s == second && option.After(after) && (best.IsZero() || option.Before(best)) {
			best = option
		}
	}
	return best
}
func dayMatches(spec calendarValue, year int, month time.Month, day int) bool {
	dom := bit(fieldMask(spec.dayOfMonth), day-1)
	dow := bit(fieldMask(spec.dayOfWeek), int(time.Date(year, month, day, 12, 0, 0, 0, spec.location).Weekday()))
	if spec.domWildcard {
		return dow
	}
	if spec.dowWildcard {
		return dom
	}
	return dom || dow
}
func daysInMonth(year int, month time.Month) int {
	return time.Date(year, month+1, 0, 12, 0, 0, 0, time.UTC).Day()
}
func bit(mask uint64, position int) bool { return mask&(uint64(1)<<uint(position)) != 0 }
func fieldMask(field FieldSet) uint64 {
	if value, ok := field.(fieldSetValue); ok {
		return value.mask
	}
	return 0
}
