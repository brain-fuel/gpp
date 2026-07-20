// Package workflow executes durable, resumable sagas. Each completed step is
// journaled before the next begins; failures retain the journal for Resume.
package workflow

import (
	"context"
	"fmt"
)

type Record struct {
	ID string `json:"id"`
	Kind string `json:"kind"`
	Next int `json:"next"`
	Done bool `json:"done"`
}
type Journal interface { Load(context.Context, string) (Record, bool, error); Save(context.Context, Record) error; Delete(context.Context, string) error }
type Step struct { Name string; Run func(context.Context) error; Compensate func(context.Context) error }
type Saga struct { ID string; Kind string; Steps []Step }

func Run(ctx context.Context, journal Journal, saga Saga) error {
	if saga.ID == "" || saga.Kind == "" { return fmt.Errorf("workflow: ID and Kind are required") }
	record, found, err := journal.Load(ctx, saga.ID)
	if err != nil { return err }
	if found && record.Kind != saga.Kind { return fmt.Errorf("workflow %q is %q, not %q", saga.ID, record.Kind, saga.Kind) }
	if !found {
		record = Record{ID: saga.ID, Kind: saga.Kind}
		if err := journal.Save(ctx, record); err != nil { return err }
	}
	for record.Next < len(saga.Steps) {
		if err := saga.Steps[record.Next].Run(ctx); err != nil { return fmt.Errorf("workflow %s step %s: %w", saga.ID, saga.Steps[record.Next].Name, err) }
		record.Next++
		if err := journal.Save(ctx, record); err != nil { return err }
	}
	record.Done = true
	return journal.Save(ctx, record)
}

func Compensate(ctx context.Context, journal Journal, saga Saga) error {
	record, found, err := journal.Load(ctx, saga.ID)
	if err != nil { return err }
	if !found { return nil }
	for i := record.Next - 1; i >= 0; i-- {
		if saga.Steps[i].Compensate != nil {
			if err := saga.Steps[i].Compensate(ctx); err != nil { return fmt.Errorf("workflow %s compensate %s: %w", saga.ID, saga.Steps[i].Name, err) }
		}
	}
	return journal.Delete(ctx, saga.ID)
}
