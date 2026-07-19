# gpp.nvim

G++ support for Neovim: filetype detection, syntax fallback, and the
`gpp lsp` server.

## Setup (lazy.nvim)

```lua
{
  dir = "path/to/gpp/editor/nvim", -- or your plugin manager's clone
  config = function()
    vim.lsp.config("gpp", {
      cmd = { "gpp", "lsp" },
      filetypes = { "gpp" },
      root_markers = { "go.mod", ".git" },
    })
    vim.lsp.enable("gpp")
  end,
}
```

`gpp` must be on PATH (`go install goforge.dev/gpp/cmd/gpp@latest`).
Install `gopls` too for hover/definition/completion; without it the
server still publishes full diagnostics.
