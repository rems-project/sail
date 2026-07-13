# LSP tests

Black-box tests for the Sail language server (`sail_lsp`). They spawn the
server as a subprocess and drive it over stdio using the JSON-RPC / LSP
`Content-Length` framing, asserting on the protocol-level behaviour.

## Running

Build the server first:

```
make lsp        # from the repository root
```

Then run the suite:

```
cd test/lsp
./run_tests.py
```

The harness locates the server binary in this order:

1. the `SAIL_LSP` environment variable, if set;
2. the binary produced by `make lsp`
   (`src/sail_lsp/_build/default/sail_lsp.exe`);
3. `sail_lsp` on `PATH`.

To test an installed server (`make lsp_install`) or a specific build:

```
SAIL_LSP=$(command -v sail_lsp) ./run_tests.py
```

Run a subset by naming the test functions:

```
./run_tests.py test_initialize test_incremental_edits
```

Results are written to `tests.xml` (the JUnit format shared with the other
Sail test suites); the runner exits non-zero if any test fails.

## Layout

- `lsp_harness.py` — a minimal LSP client: process spawning, message framing,
  request/notification helpers, and the document lifecycle (didOpen,
  didChange, didSave, didClose). Documents must exist on disk because the
  server canonicalises paths with `realpath`; use the `Workspace` helper to
  create throwaway files.
- `run_tests.py` — the test cases and runner.

## Adding a test

Add a function named `test_*` to `run_tests.py` and list it in `TESTS`. A test
constructs an `LspClient` (and usually a `Workspace`), performs a protocol
exchange, and uses `check(...)` for assertions. Each test should
`shutdown()`/`exit()` the server it starts. For example:

```python
def test_initialize():
    with LspClient() as client:
        result = client.initialize()
        check(result["serverInfo"]["name"] == "sail_lsp", "unexpected serverInfo")
        client.shutdown()
        client.exit()
```
