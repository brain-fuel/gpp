package core

import (
	"math/big"
	"sort"
	"strings"
)

// Value is the NbE semantic domain. Nat-typed values are ALWAYS kept in
// canonical linear form (VLin) — a constant plus a sum of coefficient-
// weighted atoms — so commutativity, associativity, and distribution
// over ground factors are definitional. Data values are constructor
// trees; everything stuck is a neutral.
type Value interface {
	isValue()
	String() string
}

// VLin is a nat value: Const + Σ Coef[k]·Atoms[k]. Coefficients are
// non-zero; atoms are neutral values keyed by their printed form.
// Guarded subtraction can make Const (or transient coefficients)
// negative — admissibility is the decider's business, not the form's.
type VLin struct {
	Const *big.Int
	Coef  map[string]*big.Int
	Atoms map[string]Value
}

// VCtor is first-order data.
type VCtor struct {
	Type string
	Name string
	Args []Value
}

// VNeu is a stuck computation.
type VNeu struct{ N Neutral }

// Neutral forms: a free variable, a total call stuck on a neutral
// decreasing argument, a stuck conditional, a stuck match, or a product
// of non-constant nat factors (kept opaque; the decider treats it as an
// atom that is ≥ 0).
type Neutral interface {
	isNeutral()
	String() string
}

// NVar is a free variable (a data-typed or nat-typed parameter).
type NVar struct{ Name string }

// NCall is a stuck total-function call.
type NCall struct {
	Fn   string
	Args []Value
}

// NIf is a conditional stuck on a non-ground comparison. Branches stay
// UNEVALUATED (term + captured env) — eager branch evaluation diverges
// on recursive definitions guarded by the stuck condition.
type NIf struct {
	Op         string
	L, R       Value
	Then, Else Term
	Env        Env
}

// NMatch is a match stuck on a neutral scrutinee.
type NMatch struct {
	Scrut Neutral
	Arms  []NArm
}

// NArm mirrors MatchArm with an unevaluated body (closed over an env).
type NArm struct {
	Ctor  string
	Binds []string
	Body  Term
	Env   Env
}

// NProd is a product of ≥2 non-constant nat atoms.
type NProd struct{ Factors []Value } // each factor a neutral-atom Value, sorted by String

func (VLin) isValue()  {}
func (VCtor) isValue() {}
func (VNeu) isValue()  {}

func (NVar) isNeutral()   {}
func (NCall) isNeutral()  {}
func (NIf) isNeutral()    {}
func (NMatch) isNeutral() {}
func (NProd) isNeutral()  {}

func (v VLin) String() string {
	var parts []string
	if v.Const.Sign() != 0 || len(v.Coef) == 0 {
		parts = append(parts, v.Const.String())
	}
	keys := make([]string, 0, len(v.Coef))
	for k := range v.Coef {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		c := v.Coef[k]
		if c.Cmp(big.NewInt(1)) == 0 {
			parts = append(parts, k)
		} else {
			parts = append(parts, c.String()+"*"+k)
		}
	}
	return strings.Join(parts, " + ")
}

func (v VCtor) String() string {
	if len(v.Args) == 0 {
		return v.Name
	}
	parts := make([]string, len(v.Args))
	for i, a := range v.Args {
		parts[i] = a.String()
	}
	return v.Name + "(" + strings.Join(parts, ", ") + ")"
}

func (v VNeu) String() string { return v.N.String() }

func (n NVar) String() string { return n.Name }
func (n NCall) String() string {
	parts := make([]string, len(n.Args))
	for i, a := range n.Args {
		parts[i] = a.String()
	}
	return n.Fn + "(" + strings.Join(parts, ", ") + ")"
}
func (n NIf) String() string {
	// Like NMatch: branch terms plus their captured free-variable
	// values must print, or distinct stuck ifs could compare equal.
	var b strings.Builder
	b.WriteString("if(" + n.L.String() + " " + n.Op + " " + n.R.String() + ", " + n.Then.String() + ", " + n.Else.String())
	for _, br := range []Term{n.Then, n.Else} {
		for _, fv := range FreeVars(br) {
			if v, ok := n.Env[fv]; ok {
				b.WriteString("[" + fv + "=" + v.String() + "]")
			}
		}
	}
	b.WriteString(")")
	return b.String()
}
func (n NMatch) String() string {
	// Neutral equality compares printed forms, so a stuck match must
	// print its arm bodies AND the captured values of their free
	// variables — two matches differing only in an arm body or its
	// closure must never print alike.
	var b strings.Builder
	b.WriteString("match(" + n.Scrut.String())
	for _, a := range n.Arms {
		b.WriteString("; " + a.Ctor + "(" + strings.Join(a.Binds, ",") + ")=>" + a.Body.String())
		bound := map[string]bool{}
		for _, bd := range a.Binds {
			bound[bd] = true
		}
		for _, fv := range FreeVars(a.Body) {
			if bound[fv] {
				continue
			}
			if v, ok := a.Env[fv]; ok {
				b.WriteString("[" + fv + "=" + v.String() + "]")
			}
		}
	}
	b.WriteString(")")
	return b.String()
}
func (n NProd) String() string {
	parts := make([]string, len(n.Factors))
	for i, f := range n.Factors {
		parts[i] = f.String()
	}
	return strings.Join(parts, "*")
}

// Env binds names to values.
type Env map[string]Value

// clone copies an env for arm-local extension.
func (e Env) clone() Env {
	out := make(Env, len(e)+2)
	for k, v := range e {
		out[k] = v
	}
	return out
}

// NatVar and DataVar build neutral parameter values in the right
// representation for their sort.
func NatVar(name string) Value  { return linAtom(VNeu{N: NVar{Name: name}}) }
func DataVar(name string) Value { return VNeu{N: NVar{Name: name}} }

// NatConst builds a ground nat value.
func NatConst(n int64) Value { return linConst(big.NewInt(n)) }

func linConst(c *big.Int) VLin {
	return VLin{Const: new(big.Int).Set(c), Coef: map[string]*big.Int{}, Atoms: map[string]Value{}}
}

// linAtom lifts a neutral value into a one-atom linear form.
func linAtom(v Value) VLin {
	k := v.String()
	return VLin{
		Const: new(big.Int),
		Coef:  map[string]*big.Int{k: big.NewInt(1)},
		Atoms: map[string]Value{k: v},
	}
}

// asLin coerces a nat-sorted value into linear form (neutrals atomize).
func asLin(v Value) VLin {
	switch x := v.(type) {
	case VLin:
		return x
	default:
		return linAtom(v)
	}
}

// linAdd returns a + s·b for s = ±1.
func linAdd(a, b VLin, s int64) VLin {
	out := linConst(a.Const)
	for k, c := range a.Coef {
		out.Coef[k] = new(big.Int).Set(c)
		out.Atoms[k] = a.Atoms[k]
	}
	sign := big.NewInt(s)
	out.Const.Add(out.Const, new(big.Int).Mul(sign, b.Const))
	for k, c := range b.Coef {
		add := new(big.Int).Mul(sign, c)
		if prev, ok := out.Coef[k]; ok {
			prev.Add(prev, add)
			if prev.Sign() == 0 {
				delete(out.Coef, k)
				delete(out.Atoms, k)
			}
		} else {
			out.Coef[k] = add
			out.Atoms[k] = b.Atoms[k]
		}
	}
	return out
}

// linMul multiplies two linear forms, distributing ground factors and
// atomizing products of non-constant parts.
func linMul(a, b VLin) VLin {
	out := linConst(new(big.Int).Mul(a.Const, b.Const))
	addScaled := func(dst VLin, src VLin, factor *big.Int) VLin {
		if factor.Sign() == 0 {
			return dst
		}
		scaled := linConst(big.NewInt(0))
		for k, c := range src.Coef {
			scaled.Coef[k] = new(big.Int).Mul(c, factor)
			scaled.Atoms[k] = src.Atoms[k]
		}
		return linAdd(dst, scaled, 1)
	}
	out = addScaled(out, b, a.Const) // a.Const · b.atoms — wait: b's atoms only
	out = addScaled(out, a, b.Const) // b.Const · a.atoms
	// cross products of atoms: opaque nonlinear atoms.
	for ka, ca := range a.Coef {
		for kb, cb := range b.Coef {
			factors := []Value{a.Atoms[ka], b.Atoms[kb]}
			sort.Slice(factors, func(i, j int) bool { return factors[i].String() < factors[j].String() })
			prod := VNeu{N: NProd{Factors: factors}}
			k := prod.String()
			c := new(big.Int).Mul(ca, cb)
			if prev, ok := out.Coef[k]; ok {
				prev.Add(prev, c)
				if prev.Sign() == 0 {
					delete(out.Coef, k)
					delete(out.Atoms, k)
				}
			} else {
				out.Coef[k] = c
				out.Atoms[k] = prod
			}
		}
	}
	return out
}

// ground reports whether v is a constant nat.
func ground(v VLin) bool { return len(v.Coef) == 0 }
