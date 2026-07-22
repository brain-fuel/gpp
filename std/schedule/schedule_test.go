package schedule

import (
	"testing"
	"time"

	upstream "github.com/robfig/cron/v3"
)

func parsedStandard(t *testing.T, spec string, location *time.Location) Schedule {
	t.Helper()
	result := ParseStandardInLocation(spec, location)
	parsed, ok := result.(Parsed)
	if !ok {
		t.Fatalf("parse %q: %#v", spec, result)
	}
	return parsed.Value
}
func parsedSeconds(t *testing.T, spec string, location *time.Location) Schedule {
	t.Helper()
	result := ParseSecondsInLocation(spec, location)
	parsed, ok := result.(Parsed)
	if !ok {
		t.Fatalf("parse %q: %#v", spec, result)
	}
	return parsed.Value
}
func nextTime(t *testing.T, result NextResult) time.Time {
	t.Helper()
	next, ok := result.(NextAt)
	if !ok {
		t.Fatalf("next: %#v", result)
	}
	return next.Time
}

func TestStandardDifferentialCorpus(t *testing.T) {
	location := time.UTC
	parser := upstream.NewParser(upstream.Minute | upstream.Hour | upstream.Dom | upstream.Month | upstream.Dow | upstream.Descriptor)
	tests := []struct {
		spec  string
		after time.Time
	}{{"*/5 * * * *", time.Date(2026, 1, 2, 3, 4, 30, 0, location)}, {"15 9-17 * JAN,MAR MON-FRI", time.Date(2026, 1, 2, 17, 16, 0, 0, location)}, {"0 0 29 2 *", time.Date(2025, 3, 1, 0, 0, 0, 0, location)}, {"@weekly", time.Date(2026, 1, 2, 0, 0, 0, 0, location)}, {"CRON_TZ=America/New_York 30 8 * * 1-5", time.Date(2026, 5, 1, 12, 0, 0, 0, location)}}
	for _, test := range tests {
		t.Run(test.spec, func(t *testing.T) {
			ours := parsedStandard(t, test.spec, location)
			theirs, err := parser.Parse(test.spec)
			if err != nil {
				t.Fatal(err)
			}
			got, want := nextTime(t, NextStandard(ours, test.after)), theirs.Next(test.after)
			if !got.Equal(want) {
				t.Fatalf("got %s want %s", got, want)
			}
		})
	}
}

func TestSecondsDifferentialCorpus(t *testing.T) {
	parser := upstream.NewParser(upstream.Second | upstream.Minute | upstream.Hour | upstream.Dom | upstream.Month | upstream.Dow | upstream.Descriptor)
	after := time.Date(2026, 2, 3, 4, 5, 6, 0, time.UTC)
	for _, spec := range []string{"*/7 * * * * *", "5 4 3 * * *", "@every 90s", "@every 500ms", "@every 1500ms"} {
		ours := parsedSeconds(t, spec, time.UTC)
		theirs, err := parser.Parse(spec)
		if err != nil {
			t.Fatal(err)
		}
		got, want := nextTime(t, NextSeconds(ours, after)), theirs.Next(after)
		if !got.Equal(want) {
			t.Fatalf("%s: got %s want %s", spec, got, want)
		}
	}
}

func TestDSTTransitionsMatchUpstream(t *testing.T) {
	location, err := time.LoadLocation("America/New_York")
	if err != nil {
		t.Fatal(err)
	}
	parser := upstream.NewParser(upstream.Minute | upstream.Hour | upstream.Dom | upstream.Month | upstream.Dow)
	tests := []struct {
		spec  string
		after time.Time
	}{{"30 2 * * *", time.Date(2026, 3, 8, 0, 0, 0, 0, location)}, {"30 1 * * *", time.Date(2026, 11, 1, 0, 0, 0, 0, location)}, {"30 1 * * *", time.Date(2026, 11, 1, 1, 45, 0, 0, location)}}
	for _, test := range tests {
		ours := parsedStandard(t, test.spec, location)
		theirs, err := parser.Parse(test.spec)
		if err != nil {
			t.Fatal(err)
		}
		got, want := nextTime(t, NextStandard(ours, test.after)), theirs.Next(test.after)
		if !got.Equal(want) {
			t.Fatalf("%s after %s: got %s want %s", test.spec, test.after, got, want)
		}
	}
}

func TestParserRejections(t *testing.T) {
	for _, spec := range []string{"", "* * * *", "60 * * * *", "* 24 * * *", "* * 0 * *", "* * * FOO *", "*/0 * * * *", "* * * * 7"} {
		if _, ok := ParseStandard(spec).(Rejected); !ok {
			t.Errorf("%q accepted", spec)
		}
	}
}

func TestParserAllocationReductionGate(t *testing.T) {
	const spec = "*/5 9-17 * JAN,MAR MON-FRI"
	upstreamAllocs := testing.AllocsPerRun(1000, func() {
		if _, err := upstream.ParseStandard(spec); err != nil {
			t.Fatal(err)
		}
	})
	goforgeAllocs := testing.AllocsPerRun(1000, func() {
		if _, ok := ParseStandard(spec).(Parsed); !ok {
			t.Fatal("parse failed")
		}
	})
	if goforgeAllocs*2 > upstreamAllocs {
		t.Fatalf("allocation reduction below 50%%: upstream %.0f, GoForge %.0f", upstreamAllocs, goforgeAllocs)
	}
}

func TestErasedGoBoundaryRechecksGrammarWitness(t *testing.T) {
	standard := parsedStandard(t, "* * * * *", time.UTC)
	if result, ok := NextSeconds(standard, time.Now()).(NoNext); !ok || result.Reason != "schedule grammar witness mismatch" {
		t.Fatalf("erased mismatch = %#v", result)
	}
}

func TestDynamicParsePackagesGrammarExistential(t *testing.T) {
	result := ParseDynamic("*/10 * * * * *", SecondsGrammar{})
	parsed, ok := result.(DynamicallyParsed)
	if !ok {
		t.Fatalf("dynamic parse = %#v", result)
	}
	seconds, ok := parsed.Value.(SecondsSchedule)
	if !ok {
		t.Fatalf("existential = %#v", parsed.Value)
	}
	after := time.Date(2026, 7, 21, 12, 0, 1, 0, time.UTC)
	if next, ok := NextSeconds(seconds.Value, after).(NextAt); !ok || next.Time.Second() != 10 {
		t.Fatalf("next = %#v", next)
	}
}

var benchmarkSchedule Schedule
var benchmarkUpstream upstream.Schedule

func BenchmarkParseStandard(b *testing.B) {
	const spec = "*/5 9-17 * JAN,MAR MON-FRI"
	b.Run("upstream", func(b *testing.B) {
		b.ReportAllocs()
		for b.Loop() {
			value, err := upstream.ParseStandard(spec)
			if err != nil {
				b.Fatal(err)
			}
			benchmarkUpstream = value
		}
	})
	b.Run("goforge", func(b *testing.B) {
		b.ReportAllocs()
		for b.Loop() {
			value := ParseStandard(spec)
			parsed, ok := value.(Parsed)
			if !ok {
				b.Fatal(value)
			}
			benchmarkSchedule = parsed.Value
		}
	})
}
