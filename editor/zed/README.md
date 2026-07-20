# Go+ for Zed

A dev extension: `zed: install dev extension` → select this directory.
Highlighting reuses Zed's Go grammar (Go+ is a strict superset; goplus
constructs render plainly until tree-sitter-goplus lands); the language
experience comes from `goplus lsp` — diagnostics as you type, and
hover/definition/completion when `gopls` is installed.
