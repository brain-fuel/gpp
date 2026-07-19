package registry

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"strings"
)

// Dependent function signatures (v0.7.0). A function whose parameters
// carry quantities or whose signature mentions nat erases to plain Go:
// nat becomes int, 0-quantity parameters vanish (their arguments drop
// at every call site), and the ORIGINAL signature travels in a
// //gpp:dep marker above the erased func.

// DepPrefix is the marker directive.
const DepPrefix = "//gpp:dep"

// DepParam is one parameter of the original dependent signature.
type DepParam struct {
	Quantity string // "", "0", "1", or a multiplicity variable
	Name     string
	Type     string // original type text (nat, Vec[T, n], …)
}

// DepFn is one dependent function.
type DepFn struct {
	PkgPath string
	Name    string
	Sig     string // original signature text after the name, e.g. "[T any](0 n nat, v Vec[T, n+1]) T"
	Params  []DepParam
	Result  string // original result text ("" if none)
	Dropped []int  // flattened value-parameter positions erased at calls
}

func (d *DepFn) Key() string { return d.PkgPath + "." + d.Name }

type depIndex struct {
	byKey map[string]*DepFn
}

func (r *Registry) deps() *depIndex {
	if r.depIdx == nil {
		r.depIdx = &depIndex{byKey: map[string]*DepFn{}}
	}
	return r.depIdx
}

// AddDepFn registers one dependent function.
func (r *Registry) AddDepFn(d *DepFn) error {
	idx := r.deps()
	if prev, ok := idx.byKey[d.Key()]; ok && prev.Sig != d.Sig {
		return fmt.Errorf("conflicting dep markers for %s", d.Key())
	}
	idx.byKey[d.Key()] = d
	return nil
}

// LookupDepFn finds a dependent function.
func (r *Registry) LookupDepFn(pkgPath, name string) (*DepFn, bool) {
	d, ok := r.deps().byKey[pkgPath+"."+name]
	return d, ok
}

// ParseDepSig parses the marker's signature text into parameters and
// result. The text is "Name[tparams](params) result" with quantity
// prefixes preserved.
func ParseDepSig(pkgPath, sig string) (*DepFn, error) {
	nameEnd := strings.IndexAny(sig, "[(")
	if nameEnd < 0 {
		return nil, fmt.Errorf("malformed dep signature %q", sig)
	}
	d := &DepFn{PkgPath: pkgPath, Name: strings.TrimSpace(sig[:nameEnd]), Sig: strings.TrimSpace(sig[nameEnd:])}
	rest := sig[nameEnd:]
	if strings.HasPrefix(rest, "[") {
		close := matchBracket(rest, 0)
		if close < 0 {
			return nil, fmt.Errorf("malformed dep signature %q", sig)
		}
		rest = rest[close+1:]
	}
	rest = strings.TrimSpace(rest)
	if !strings.HasPrefix(rest, "(") {
		return nil, fmt.Errorf("malformed dep signature %q", sig)
	}
	close := matchParen(rest, 0)
	if close < 0 {
		return nil, fmt.Errorf("malformed dep signature %q", sig)
	}
	paramsText := rest[1:close]
	d.Result = strings.TrimSpace(rest[close+1:])
	pos := 0
	for _, part := range splitTopLevel(paramsText, ',') {
		fields := strings.Fields(strings.TrimSpace(part))
		if len(fields) == 0 {
			continue
		}
		q := ""
		if fields[0] == "0" || fields[0] == "1" {
			q = fields[0]
			fields = fields[1:]
		}
		if len(fields) < 2 {
			// shared-type groups ("a, b nat") arrive as bare names; the
			// marker writer flattens, so treat as malformed here.
			return nil, fmt.Errorf("dep signature %q: parameter %q not in 'name Type' form", sig, part)
		}
		d.Params = append(d.Params, DepParam{Quantity: q, Name: fields[0], Type: strings.Join(fields[1:], " ")})
		if q == "0" {
			d.Dropped = append(d.Dropped, pos)
		}
		pos++
	}
	return d, nil
}

// matchParen finds the ) matching the ( at position open.
func matchParen(s string, open int) int {
	depth := 0
	for i := open; i < len(s); i++ {
		switch s[i] {
		case '(':
			depth++
		case ')':
			depth--
			if depth == 0 {
				return i
			}
		}
	}
	return -1
}

// DepFnsFromMarkers reconstructs dependent functions from one generated
// file.
func DepFnsFromMarkers(pkgPath, filename string, src []byte) ([]*DepFn, error) {
	if !strings.Contains(string(src), DepPrefix) {
		return nil, nil
	}
	fset := token.NewFileSet()
	astFile, err := parser.ParseFile(fset, filename, src, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		return nil, fmt.Errorf("parsing %s for gpp markers: %w", filename, err)
	}
	var out []*DepFn
	for _, decl := range astFile.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Doc == nil || fd.Recv != nil {
			continue
		}
		for _, c := range fd.Doc.List {
			rest, ok := strings.CutPrefix(c.Text, DepPrefix+" ")
			if !ok {
				continue
			}
			d, err := ParseDepSig(pkgPath, strings.TrimSpace(rest))
			if err != nil {
				return nil, fmt.Errorf("%s: %v", filename, err)
			}
			if d.Name != fd.Name.Name {
				return nil, fmt.Errorf("%s: dep marker %q does not match func %s", filename, rest, fd.Name.Name)
			}
			out = append(out, d)
		}
	}
	return out, nil
}
