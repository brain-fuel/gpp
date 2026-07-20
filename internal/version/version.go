// Package version is the single source of the toolchain version — a
// leaf package so both the CLI and the emitter (which stamps generated
// files) can share it without cycles.
package version

import (
	"strconv"
	"strings"
)

// Version is the goplus toolchain version.
const Version = "v0.16.0"

// Newer reports whether a is a strictly newer release than b. Inputs
// are "vMAJOR.MINOR.PATCH"; anything unparseable compares as not newer
// (conservative: unknown vintages never block).
func Newer(a, b string) bool {
	pa, oka := parts(a)
	pb, okb := parts(b)
	if !oka || !okb {
		return false
	}
	for i := 0; i < 3; i++ {
		if pa[i] != pb[i] {
			return pa[i] > pb[i]
		}
	}
	return false
}

func parts(v string) ([3]int, bool) {
	v = strings.TrimPrefix(strings.TrimSpace(v), "v")
	segs := strings.SplitN(v, ".", 3)
	if len(segs) != 3 {
		return [3]int{}, false
	}
	var out [3]int
	for i, s := range segs {
		n, err := strconv.Atoi(strings.TrimSuffix(s, "\n"))
		if err != nil {
			return [3]int{}, false
		}
		out[i] = n
	}
	return out, true
}
