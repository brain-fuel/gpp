// Package semver parses, compares, and increments Semantic Versioning 2.0.0
// versions without imposing a leading-v convention.
package semver

import (
	"fmt"
	"strconv"
	"strings"
)

type Version struct {
	Major uint64
	Minor uint64
	Patch uint64
	Pre   []string
	Build []string
}

func Parse(s string) (Version, error) {
	var v Version
	if s == "" || strings.HasPrefix(s, "v") {
		return v, fmt.Errorf("invalid semantic version %q", s)
	}
	core := s
	if i := strings.IndexByte(core, '+'); i >= 0 {
		v.Build = strings.Split(core[i+1:], ".")
		if err := validIdentifiers(v.Build, false); err != nil {
			return Version{}, err
		}
		core = core[:i]
	}
	if i := strings.IndexByte(core, '-'); i >= 0 {
		v.Pre = strings.Split(core[i+1:], ".")
		if err := validIdentifiers(v.Pre, true); err != nil {
			return Version{}, err
		}
		core = core[:i]
	}
	parts := strings.Split(core, ".")
	if len(parts) != 3 { return Version{}, fmt.Errorf("invalid semantic version %q", s) }
	values := []*uint64{&v.Major, &v.Minor, &v.Patch}
	for i, part := range parts {
		if part == "" || len(part) > 1 && part[0] == '0' { return Version{}, fmt.Errorf("invalid numeric identifier %q", part) }
		n, err := strconv.ParseUint(part, 10, 64)
		if err != nil { return Version{}, fmt.Errorf("invalid numeric identifier %q", part) }
		*values[i] = n
	}
	return v, nil
}

func MustParse(s string) Version {
	v, err := Parse(s)
	if err != nil {
		panic(err)
	}
	return v
}

func validIdentifiers(ids []string, rejectLeadingZero bool) error {
	if len(ids) == 0 { return fmt.Errorf("empty identifier") }
	for _, id := range ids {
		if id == "" { return fmt.Errorf("empty identifier") }
		numeric := true
		for _, r := range id {
			if !((r >= '0' && r <= '9') || (r >= 'A' && r <= 'Z') || (r >= 'a' && r <= 'z') || r == '-') { return fmt.Errorf("invalid identifier %q", id) }
			if r < '0' || r > '9' { numeric = false }
		}
		if rejectLeadingZero && numeric && len(id) > 1 && id[0] == '0' { return fmt.Errorf("numeric prerelease identifier %q has a leading zero", id) }
	}
	return nil
}

func (v Version) String() string {
	s := fmt.Sprintf("%d.%d.%d", v.Major, v.Minor, v.Patch)
	if len(v.Pre) > 0 { s += "-" + strings.Join(v.Pre, ".") }
	if len(v.Build) > 0 { s += "+" + strings.Join(v.Build, ".") }
	return s
}

func (v Version) Compare(o Version) int {
	if v.Major != o.Major {
		if v.Major < o.Major { return -1 }
		return 1
	}
	if v.Minor != o.Minor {
		if v.Minor < o.Minor { return -1 }
		return 1
	}
	if v.Patch != o.Patch {
		if v.Patch < o.Patch { return -1 }
		return 1
	}
	if len(v.Pre) == 0 && len(o.Pre) == 0 { return 0 }
	if len(v.Pre) == 0 { return 1 }
	if len(o.Pre) == 0 { return -1 }
	for i := 0; i < len(v.Pre) && i < len(o.Pre); i++ {
		a, b := v.Pre[i], o.Pre[i]
		if a == b { continue }
		an, ae := strconv.ParseUint(a, 10, 64)
		bn, be := strconv.ParseUint(b, 10, 64)
		if ae == nil && be == nil {
			if an < bn { return -1 }
			return 1
		}
		if ae == nil { return -1 }
		if be == nil { return 1 }
		if a < b { return -1 }
		return 1
	}
	if len(v.Pre) < len(o.Pre) { return -1 }
	if len(v.Pre) > len(o.Pre) { return 1 }
	return 0
}

func (v Version) BumpMajor() Version { return Version{Major: v.Major + 1} }
func (v Version) BumpMinor() Version { return Version{Major: v.Major, Minor: v.Minor + 1} }
func (v Version) BumpPatch() Version { return Version{Major: v.Major, Minor: v.Minor, Patch: v.Patch + 1} }
