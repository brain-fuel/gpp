package schedule

import (
	"testing"
	"time"
)

func FuzzParseNeverPanics(f *testing.F) {
	for _, seed := range []string{"* * * * *", "*/5 9-17 * JAN,MAR MON-FRI", "@every 5m", "", "TZ=UTC 0 0 * * *"} {
		f.Add(seed)
	}
	f.Fuzz(func(t *testing.T, spec string) {
		_ = ParseStandard(spec)
		_ = ParseSeconds(spec)
	})
}

func FuzzParsedNextIsLater(f *testing.F) {
	f.Add("*/5 * * * *", int64(1_700_000_000))
	f.Add("0 0 29 2 *", int64(1_750_000_000))
	f.Fuzz(func(t *testing.T, spec string, unix int64) {
		if unix < -62_135_596_800 || unix > 253_402_300_799 {
			t.Skip()
		}
		parsed, ok := ParseStandard(spec).(Parsed)
		if !ok {
			return
		}
		after := time.Unix(unix, 0).UTC()
		if next, ok := NextStandard(parsed.Value, after).(NextAt); ok && !next.Time.After(after) {
			t.Fatalf("next %s is not after %s", next.Time, after)
		}
	})
}
