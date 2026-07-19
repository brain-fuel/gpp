# G++ for Zed

A dev extension: `zed: install dev extension` → select this directory.
Highlighting reuses Zed's Go grammar (G++ is a strict superset; gpp
constructs render plainly until tree-sitter-gpp lands); the language
experience comes from `gpp lsp` — diagnostics as you type, and
hover/definition/completion when `gopls` is installed.
