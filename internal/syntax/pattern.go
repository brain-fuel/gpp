package syntax

import (
	"fmt"
	"go/scanner"
	"go/token"
)

// PatText is a match pattern re-parsed from carrier text (the
// `//goplus:pattern <verbatim>` lines that thread pattern structure through
// the resolution fixpoint).
type PatText struct {
	Binder string // whole-value binder name; "" if absent
	Root   PatNode
	Alts   []PatNode // additional alternatives of a multi-pattern arm (v0.12.0)
}

// PatNode is one node of a textual pattern tree.
type PatNode struct {
	Wild    bool   // `_`
	Qual    string // qualifier before '.', e.g. "lib" or "Option"; "" if bare
	Name    string // constructor (or binder) name
	HasArgs bool   // distinguishes None from None()
	Args    []PatNode
}

// ParsePatternText parses "c := Circle(r)", "Add(Lit(a), _)", "_",
// "opt.Some(v)".
func ParsePatternText(text string) (PatText, error) {
	p := &patParser{}
	fset := token.NewFileSet()
	file := fset.AddFile("pattern", -1, len(text))
	p.s.Init(file, []byte(text), nil, 0)
	p.next()

	var out PatText
	// Optional binder: IDENT ":=".
	if p.tok == token.IDENT {
		save := *p
		name := p.lit
		p.next()
		if p.tok == token.DEFINE {
			out.Binder = name
			p.next()
		} else {
			*p = save
		}
	}
	root, err := p.pattern()
	if err != nil {
		return PatText{}, err
	}
	out.Root = root
	for p.tok == token.COMMA {
		p.next()
		alt, err := p.pattern()
		if err != nil {
			return PatText{}, err
		}
		out.Alts = append(out.Alts, alt)
	}
	if p.tok != token.EOF && p.tok != token.SEMICOLON {
		return PatText{}, fmt.Errorf("unexpected %s in pattern %q", p.tok, text)
	}
	return out, nil
}

type patParser struct {
	s   scanner.Scanner
	tok token.Token
	lit string
}

func (p *patParser) next() {
	_, p.tok, p.lit = p.s.Scan()
}

func (p *patParser) pattern() (PatNode, error) {
	if p.tok != token.IDENT {
		return PatNode{}, fmt.Errorf("expected pattern, found %s", p.tok)
	}
	if p.lit == "_" {
		p.next()
		return PatNode{Wild: true}, nil
	}
	n := PatNode{Name: p.lit}
	p.next()
	if p.tok == token.PERIOD {
		p.next()
		if p.tok != token.IDENT {
			return PatNode{}, fmt.Errorf("expected identifier after '.'")
		}
		n.Qual, n.Name = n.Name, p.lit
		p.next()
	}
	if p.tok == token.LPAREN {
		n.HasArgs = true
		p.next()
		for p.tok != token.RPAREN && p.tok != token.EOF {
			arg, err := p.pattern()
			if err != nil {
				return PatNode{}, err
			}
			n.Args = append(n.Args, arg)
			if p.tok == token.COMMA {
				p.next()
				continue
			}
			break
		}
		if p.tok != token.RPAREN {
			return PatNode{}, fmt.Errorf("missing ')' in pattern")
		}
		p.next()
	}
	return n, nil
}

// String renders a PatNode back to pattern text (for witness diagnostics).
func (n PatNode) String() string {
	if n.Wild {
		return "_"
	}
	out := n.Name
	if n.Qual != "" {
		out = n.Qual + "." + n.Name
	}
	if n.HasArgs || len(n.Args) > 0 {
		out += "("
		for i, a := range n.Args {
			if i > 0 {
				out += ", "
			}
			out += a.String()
		}
		out += ")"
	}
	return out
}
