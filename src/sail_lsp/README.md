sail_lsp
========

### Usage

This is a minimal (and highly WIP) LSP server for Sail.

Currently supports syntax highlighting, code folding, hover
type-at-cursor, go-to-definition, and reporting type-error
diagnostics as you type.

No editor modes are currently provided, but it is particularly easy to
set up in neovim for testing with just the following lua:

```lua

vim.lsp.config['sail_lsp'] = {
    cmd = { 'sail_lsp', '--stdio' },
    filetypes = { 'sail' },
    root_markers = { '.git' },
    settings = {}
}

vim.lsp.enable('sail_lsp')

vim.filetype.add({
    extension = {
        sail = "sail",
    },
})
```

### Build

Use `make lsp` or `make lsp_install` from the repository root.
Currently the LSP is set up as a separate dune-project, so it will use
the _installed_ version of `Libsail`.

### Testing

There is a python script (mostly vibe-coded) that can drive the LSP
protocol for testing, and tests in `test/lsp` at the repository root.

For testing the UTF-16 support in Libsail, there are also unit tests
in `test/unit` which are gated behind setting the
`SAIL_UNIT_TESTS=true` enviroment variable.
