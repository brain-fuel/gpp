# goplus.nvim

Go+ support for Neovim: filetype detection, syntax fallback, and the
`goplus lsp` server.

## Setup (lazy.nvim)

```lua
{
  dir = "path/to/goplus/editor/nvim", -- or your plugin manager's clone
  config = function()
    vim.lsp.config("goplus", {
      cmd = { "goplus", "lsp" },
      filetypes = { "goplus" },
      root_markers = { "go.mod", ".git" },
    })
    vim.lsp.enable("goplus")
  end,
}
```

`goplus` must be on PATH (`go install goforge.dev/goplus/cmd/goplus@latest`).
Install `gopls` too for hover/definition/completion; without it the
server still publishes full diagnostics.
