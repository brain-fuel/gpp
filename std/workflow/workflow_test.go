package workflow

import (
	"context"
	"errors"
	"path/filepath"
	"testing"
	"time"

	"goforge.dev/goplus/std/schedule"
)

type memoryJournal struct{ records map[string]Record }

func (m *memoryJournal) Load(_ context.Context, id string) (Record, bool, error) {
	r, ok := m.records[id]
	return r, ok, nil
}

func TestFileJournalRoundTrip(t *testing.T) {
	j := FileJournal{Dir: filepath.Join(t.TempDir(), "journal")}
	r := Record{ID: "release-1", Kind: "release", Next: 2}
	if err := j.Save(context.Background(), r); err != nil {
		t.Fatal(err)
	}
	got, ok, err := j.Load(context.Background(), r.ID)
	if err != nil || !ok || got != r {
		t.Fatalf("Load = %+v, %v, %v", got, ok, err)
	}
}
func (m *memoryJournal) Save(_ context.Context, r Record) error    { m.records[r.ID] = r; return nil }
func (m *memoryJournal) Delete(_ context.Context, id string) error { delete(m.records, id); return nil }

func TestRunResumesAtFirstIncompleteStep(t *testing.T) {
	j := &memoryJournal{records: map[string]Record{}}
	n, fail := 0, true
	s := Saga{ID: "release-1", Kind: "release", Steps: []Step{
		{Name: "metadata", Run: func(context.Context) error { n++; return nil }},
		{Name: "tag", Run: func(context.Context) error {
			if fail {
				return errors.New("changed")
			}
			n++
			return nil
		}},
	}}
	if err := Run(context.Background(), j, s); err == nil {
		t.Fatal("first run succeeded")
	}
	fail = false
	if err := Run(context.Background(), j, s); err != nil {
		t.Fatal(err)
	}
	if n != 2 || !j.records[s.ID].Done {
		t.Fatalf("n=%d record=%+v", n, j.records[s.ID])
	}
}

func TestScheduledWorkflowUsesValidatedSchedule(t *testing.T) {
	parsed, ok := schedule.ParseStandardInLocation("*/15 * * * *", time.UTC).(schedule.Parsed)
	if !ok {
		t.Fatal("schedule did not parse")
	}
	after := time.Date(2026, 7, 21, 12, 1, 0, 0, time.UTC)
	next, ok := NextStandardStart(Saga{ID: "report", Kind: "report"}, parsed.Value, after).(schedule.NextAt)
	if !ok || !next.Time.Equal(time.Date(2026, 7, 21, 12, 15, 0, 0, time.UTC)) {
		t.Fatalf("next = %#v", next)
	}
}
