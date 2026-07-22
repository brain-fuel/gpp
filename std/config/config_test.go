package config

import (
	"errors"
	"strings"
	"testing"
)

type testDecoder struct{}

func (testDecoder) Decode(_ []byte, base int) (int, error) { return base + 1, nil }

func TestFieldErrorsCollectPaths(t *testing.T) {
	err := Collect(At("release.tag", errors.New("required")), At("locks.ttl", errors.New("invalid")))
	if got := err.Error(); !strings.Contains(got, "release.tag: required") || !strings.Contains(got, "locks.ttl: invalid") {
		t.Fatal(got)
	}
}

func TestSchemaAppliesDefaultsBeforeDecode(t *testing.T) {
	v, err := (Schema[int]{Defaults: func() int { return 41 }, Decoder: testDecoder{}}).Load(nil)
	if err != nil || v != 42 {
		t.Fatalf("Load = %d, %v", v, err)
	}
}

func TestResolvePrecedenceProvenanceAndOwnership(t *testing.T) {
	defaults := map[string]any{"port": 80, "nested": []string{"owned"}}
	snapshot := Resolve(7,
		Layer{Source: DefaultSource{}, Values: defaults},
		Layer{Source: FileSource{}, Values: map[string]any{"port": 8080}},
		Layer{Source: EnvironmentSource{}, Values: map[string]any{"port": 9000}},
		Layer{Source: FlagSource{}, Values: map[string]any{"port": 10000}},
		Layer{Source: OverrideSource{}, Values: map[string]any{"port": 11000}},
	)
	port := NewKey(7, "PORT", func(value any) (int, bool) { n, ok := value.(int); return n, ok })
	got := Get(snapshot, port)
	found, ok := got.(Found[int])
	if !ok || found.Value != 11000 || !SourceEqual(found.Source, OverrideSource{}) {
		t.Fatalf("Get = %#v", got)
	}
	defaults["port"] = -1
	entry, _ := Untyped(snapshot, "port")
	if entry.Value != 11000 {
		t.Fatalf("snapshot aliased input: %#v", entry)
	}
	nested, _ := Untyped(snapshot, "nested")
	nested.Value.([]string)[0] = "mutated"
	again, _ := Untyped(snapshot, "nested")
	if again.Value.([]string)[0] != "owned" {
		t.Fatal("Untyped exposed snapshot storage")
	}
}

func TestTypedLookupDistinguishesMissingAndWrongType(t *testing.T) {
	snapshot := Resolve(2, Layer{Source: FileSource{}, Values: map[string]any{"port": "bad"}})
	port := NewKey(2, "port", func(value any) (int, bool) { n, ok := value.(int); return n, ok })
	if _, ok := Get(snapshot, port).(WrongType[int]); !ok {
		t.Fatal("expected WrongType")
	}
	missing := NewKey(2, "missing", func(value any) (int, bool) { n, ok := value.(int); return n, ok })
	if _, ok := Get(snapshot, missing).(Missing[int]); !ok {
		t.Fatal("expected Missing")
	}
}

func TestPlainGoSchemaGuard(t *testing.T) {
	snapshot := Resolve(1)
	key := NewKey(2, "port", func(value any) (int, bool) { n, ok := value.(int); return n, ok })
	defer func() {
		if recover() == nil {
			t.Fatal("schema mismatch did not panic")
		}
	}()
	_ = Get(snapshot, key)
}

func TestRequireProducesEvidenceAndProjectRetypesSubset(t *testing.T) {
	snapshot := Resolve(10, Layer{Source: FileSource{}, Values: map[string]any{"port": 8080, "secret": "hidden"}})
	port := NewKey(10, "port", func(value any) (int, bool) { n, ok := value.(int); return n, ok })
	requirement := Require(snapshot, port)
	available, ok := requirement.(Available[int])
	if !ok || RequiredValue(available.Present) != 8080 {
		t.Fatalf("Require = %#v", requirement)
	}
	public := Project(snapshot, NewSubset(10, 11, "port"))
	if _, ok := Untyped(public, "port"); !ok {
		t.Fatal("projected key missing")
	}
	if _, ok := Untyped(public, "secret"); ok {
		t.Fatal("projection leaked omitted key")
	}
}
