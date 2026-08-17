sail_lsp
========

### Usage

This is a minimal (and highly WIP) LSP server for Sail.

Currently supports syntax highlighting, code folding, hover
type-at-cursor, go-to-definition, automatic formatting, and reporting
type-error diagnostics as you type.

### Configuration

Semantic highlighting and folding are off by default. Either can be
turned on with a command line flag (`--highlight` and `--folding`, plus
the matching `--no-` flags), or in the configuration file, which is
read from `$XDG_CONFIG_HOME/sail_lsp/config.json`
(`%APPDATA%\sail_lsp\config.json` on Windows). A flag on the command
line overrides the file.

```json
{
    "sail_dir": "/path/to/sail",
    "highlight": true,
    "fmt": {
        "indent": 4,
        "line_width": 120
    }
}
```

The `fmt` section holds the formatting options, and takes the same
keys as the `fmt` section of a Sail configuration file passed to `sail
-fmt`.

Formatting works on whole documents and on selections. A selection is
formatted a definition at a time: every definition the selection
touches is reformatted, so putting the cursor in a definition and
formatting the selection reformats just that definition. Whatever lies
between definitions — a comment on a line of its own, say — belongs to
no definition, and is left as written.

Either way the whole buffer has to parse, because a definition is
formatted by formatting the document it belongs to and keeping the part
that corresponds to it. A document that does not parse cannot be
formatted, and the server responds with an error explaining why rather
than silently leaving the buffer alone.

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

For emacs, if using `lsp-mode`, you can add the following to your
`.emacs` file after loading `sail-mode`:

```elisp
(require 'lsp-mode)
(add-to-list 'lsp-language-id-configuration '(sail-mode . "sail"))
(lsp-register-client (make-lsp-client
                      :new-connection (lsp-stdio-connection "sail_lsp")
                      :activation-fn (lsp-activate-on "sail")
                      :server-id 'saillsp))
```

When using `eglot` in emacs, the corresponding snippet after loading
`sail-mode` is:

``` elisp
(add-hook 'sail-mode-hook 'eglot-ensure)
(with-eval-after-load 'eglot
  (add-to-list 'eglot-server-programs
	       '((sail-mode :language-id "Sail") . ("sail_lsp"))))
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
