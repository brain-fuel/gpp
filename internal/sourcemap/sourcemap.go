// Package sourcemap maps positions in emitted Go back to .gpp source.
//
// Because emission is text-edit-based (intra-line splices plus inserted
// header/marker lines) and then gofmt-formatted, a line-level diff between
// source and output recovers an accurate mapping: unchanged lines map
// exactly, spliced lines map with line fidelity, inserted lines attribute
// to the nearest preceding mapped line.
package sourcemap

import (
	"go/token"
	"strings"
)

// Map maps one emitted file's positions to its .gpp source.
type Map struct {
	GppPath string
	// gppLine[i] is the 1-based .gpp line for emitted line i+1; 0 for
	// inserted lines with no counterpart.
	gppLine []int
	// exact[i]: the line text is identical, so columns carry over.
	exact []bool
}

// Build diffs gpp source against emitted output.
func Build(gppPath string, gppSrc, emitted []byte) *Map {
	a := splitLines(gppSrc)
	b := splitLines(emitted)
	m := &Map{GppPath: gppPath, gppLine: make([]int, len(b)), exact: make([]bool, len(b))}

	// Patience-style anchoring: only lines whose text is UNIQUE in both
	// files anchor (then the longest increasing chain of those pairs).
	// Plain line-LCS mis-anchors when generated-only blocks (derived
	// folds, delegation forwarders) contain lines textually identical to
	// source lines — `case Heads:`, closing braces — dragging the map
	// off the real correspondence.
	const cap = 5000
	if len(a) > cap || len(b) > cap {
		for i := range b {
			if i < len(a) {
				m.gppLine[i] = i + 1
			}
		}
		return m
	}
	countA := map[string]int{}
	countB := map[string]int{}
	posA := map[string]int{}
	for i, l := range a {
		countA[l]++
		posA[l] = i
	}
	for _, l := range b {
		countB[l]++
	}
	type pair struct{ ai, bj int }
	var pairs []pair
	for j, l := range b {
		if strings.TrimSpace(l) == "" {
			continue
		}
		if countA[l] == 1 && countB[l] == 1 {
			pairs = append(pairs, pair{ai: posA[l], bj: j})
		}
	}
	// pairs are increasing in bj; take the longest increasing subsequence
	// in ai (patience sorting).
	if len(pairs) > 0 {
		tails := []int{} // indices into pairs: last element of each pile chain
		links := make([]int, len(pairs))
		for idx := range links {
			links[idx] = -1
		}
		for idx, pr := range pairs {
			lo, hi := 0, len(tails)
			for lo < hi {
				mid := (lo + hi) / 2
				if pairs[tails[mid]].ai < pr.ai {
					lo = mid + 1
				} else {
					hi = mid
				}
			}
			if lo > 0 {
				links[idx] = tails[lo-1]
			}
			if lo == len(tails) {
				tails = append(tails, idx)
			} else {
				tails[lo] = idx
			}
		}
		for at := tails[len(tails)-1]; at >= 0; at = links[at] {
			m.gppLine[pairs[at].bj] = pairs[at].ai + 1
			m.exact[pairs[at].bj] = true
		}
	}
	// Fill runs between anchors with exact matches (non-unique lines like
	// braces still correspond when sandwiched between anchors).
	prevA, prevB := 0, 0
	for j := 0; j <= len(b); j++ {
		if j < len(b) && m.gppLine[j] == 0 {
			continue
		}
		endA := len(a)
		endB := len(b)
		if j < len(b) {
			endA = m.gppLine[j] - 1
			endB = j
		}
		ai, bj := prevA, prevB
		for ai < endA && bj < endB {
			if a[ai] == b[bj] {
				m.gppLine[bj] = ai + 1
				m.exact[bj] = true
				ai++
				bj++
				continue
			}
			// Advance the generated side first: generated-only blocks are
			// the common insertion.
			bj++
		}
		if j < len(b) {
			prevA = m.gppLine[j]
			prevB = j + 1
		}
	}

	// Second alignment pass: lowering reindents arm bodies (nested-match
	// chains, wrapped returns), so lines that differ only in leading
	// whitespace still correspond. Between anchored exact matches, align
	// remaining unmatched output lines to unmatched source lines that are
	// equal modulo leading whitespace, in order.
	srcUsed := make([]bool, len(a)+1)
	for _, ln := range m.gppLine {
		if ln > 0 {
			srcUsed[ln] = true
		}
	}
	si := 0
	for j := range m.gppLine {
		if m.gppLine[j] != 0 {
			si = m.gppLine[j] // advance the source cursor past the anchor
			continue
		}
		trimmed := strings.TrimLeft(b[j], " \t")
		if trimmed == "" {
			continue
		}
		for k := si + 1; k <= len(a) && k <= si+40; k++ {
			if srcUsed[k] {
				continue
			}
			if strings.TrimLeft(a[k-1], " \t") == trimmed {
				m.gppLine[j] = k
				srcUsed[k] = true
				si = k
				break
			}
		}
	}
	// Remaining inserted lines attribute to the previous mapped line's
	// successor region (e.g. generated headers and prologues).
	prev := 0
	for j := range m.gppLine {
		if m.gppLine[j] != 0 {
			prev = m.gppLine[j]
			continue
		}
		if prev > 0 && prev < len(a) {
			m.gppLine[j] = prev + 1
		}
	}
	return m
}

// Map translates an emitted-file position to a .gpp position. ok is false
// when the line has no plausible source counterpart (e.g. the header).
func (m *Map) Map(pos token.Position) (token.Position, bool) {
	if pos.Line < 1 || pos.Line > len(m.gppLine) || m.gppLine[pos.Line-1] == 0 {
		return token.Position{}, false
	}
	out := token.Position{
		Filename: m.GppPath,
		Line:     m.gppLine[pos.Line-1],
		Column:   pos.Column,
	}
	if !m.exact[pos.Line-1] && out.Column > 1 {
		// Spliced line: the column may not correspond; keep it as a hint.
	}
	return out, true
}

func splitLines(b []byte) []string {
	var lines []string
	start := 0
	for i := 0; i < len(b); i++ {
		if b[i] == '\n' {
			lines = append(lines, string(b[start:i]))
			start = i + 1
		}
	}
	if start < len(b) {
		lines = append(lines, string(b[start:]))
	}
	return lines
}
