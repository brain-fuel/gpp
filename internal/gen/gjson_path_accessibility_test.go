package gen

import (
	"path/filepath"
	"strings"
	"testing"
)

func gjsonConsumerModule(t *testing.T, source string) string {
	t.Helper()
	dir := t.TempDir()
	gjson, err := filepath.Abs("../../../gjson")
	if err != nil {
		t.Fatal(err)
	}
	std, err := filepath.Abs("../../std")
	if err != nil {
		t.Fatal(err)
	}
	writeRefinementTestFile(t, dir, "go.mod", "module example.com/gjsonproof\n\ngo 1.25.0\n\nrequire (\n goforge.dev/gjson v0.0.0\n goforge.dev/goplus/std v0.0.0\n)\nreplace goforge.dev/gjson => "+gjson+"\nreplace goforge.dev/goplus/std => "+std+"\n")
	writeRefinementTestFile(t, dir, "main.gp", source)
	return dir
}

func TestGoPlusConsumesSchemaIndexedJSONPath(t *testing.T) {
	dir := gjsonConsumerModule(t, `package main
import (
 "goforge.dev/gjson"
 "goforge.dev/gjson/typed"
)
func main() {
 path := typed.NewPath[int](9, []typed.Segment{typed.Field("id")}, typed.IntegerKind())
 document, _ := gjson.ParseDocument("{\"id\":42}")
 bound := gjson.BindJSONDocument(9, document)
 _ = gjson.LookupInteger(9, path, bound)
}
`)
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if !res.Ok() {
		t.Fatalf("generation diagnostics: %+v", res.Diags)
	}
}

func TestSchemaIndexedJSONPathRejectsWrongSchema(t *testing.T) {
	dir := gjsonConsumerModule(t, `package main
import (
 "goforge.dev/gjson"
 "goforge.dev/gjson/typed"
)
func main() {
 path := typed.NewPath[int](9, []typed.Segment{typed.Field("id")}, typed.IntegerKind())
 document, _ := gjson.ParseDocument("{\"id\":42}")
 bound := gjson.BindJSONDocument(10, document)
 _ = gjson.LookupInteger(10, path, bound)
}
`)
	assertGJSONDependentReject(t, dir, "path from schema 9 unexpectedly queried as schema 10")
}

func TestSchemaIndexedJSONPathRejectsWrongDocument(t *testing.T) {
	dir := gjsonConsumerModule(t, `package main
import (
 "goforge.dev/gjson"
 "goforge.dev/gjson/typed"
)
func main() {
 path := typed.NewPath[int](9, []typed.Segment{typed.Field("id")}, typed.IntegerKind())
 document, _ := gjson.ParseDocument("{\"id\":42}")
 bound := gjson.BindJSONDocument(10, document)
 _ = gjson.LookupInteger(9, path, bound)
}
`)
	assertGJSONDependentReject(t, dir, "document from schema 10 unexpectedly queried by schema 9 path")
}

func TestPresenceWitnessRejectsMissingLookup(t *testing.T) {
	dir := gjsonConsumerModule(t, `package main
import "goforge.dev/gjson/typed"
func main() {
 missing := typed.Missing[int]()
 _ = typed.PresentValue(missing)
}
`)
	assertGJSONDependentReject(t, dir, "missing lookup unexpectedly accepted as present")
}

func assertGJSONDependentReject(t *testing.T, dir, message string) {
	t.Helper()
	res, err := Run(Options{Dir: dir, Patterns: []string{"."}})
	if err != nil {
		t.Fatal(err)
	}
	if res.Ok() {
		t.Fatal(message)
	}
	for _, diagnostic := range res.Diags {
		if strings.Contains(diagnostic.Msg, "index") || strings.Contains(diagnostic.Msg, "cannot unify") {
			return
		}
	}
	t.Fatalf("diagnostics do not explain dependent mismatch: %+v", res.Diags)
}
