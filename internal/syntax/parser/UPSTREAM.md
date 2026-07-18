# Vendored go/parser

`parser.go`, `interface.go`, and `resolver.go` are vendored from GOROOT
`src/go/parser` at **go1.26.5** (see the Go BSD license in `GO-LICENSE`;
original copyright headers retained). `resolver.go` is unmodified.

All gpp modifications are bracketed with `// gpp:begin` / `// gpp:end`
markers (or one-line `// gpp:` comments):

1. `parser` struct: `ahead` lookahead buffer + `ext Extensions` fields.
2. `next0`: reads tokens via `rawScan` (lookahead replay).
3. `parseFuncDecl`: method type parameters are KEPT (upstream errors and
   discards them) — G++ v0.1.0 generic methods.
4. `parseTypeSpec` / `parseGenericType`: the `spec.Type = p.parseType()`
   tail is routed through `parseTypeSpecType` (enum hook).
5. `parseStmt`: contextual `match` hook at the top.
6. `stringEnd`: computed as `pos + len(lit)` instead of the unreachable
   `go/internal/scannerhooks` backdoor. Exact except raw strings containing
   carriage returns; `ast.BasicLit.End()` applies the same fallback itself.
7. `tokPrec`: adjacency-claimed `|>` / `>>>` sequences demote to
   `token.LowestPrec`, so the stock precedence ladder returns without
   consuming them (v0.3.0 pipelines/composition).
8. `parseExpr`: tail-calls `parseExtOps` to consume claimed `|>` / `>>>`
   chains at the bottom of the ladder.

Everything new lives in `gpp.go` (grammar hooks) and `ext.go` (extension
node types + `ParseFileExt`).

## Re-vendoring

Copy the three upstream files, replay hunks 1–6 (search `gpp:`), and run
`go test ./internal/syntax/parser/` — `TestForkEquivalence` parses a pure-Go
corpus with fork and stock parser and requires identical ASTs and error
lists, so behavioral drift is detected mechanically.
