#!/usr/bin/env python3

"""Black-box test suite for the Sail LSP server (``sail_lsp``).

Each test drives a fresh server subprocess over stdio using the client in
``lsp_harness.py`` and asserts on the protocol-level behaviour.  Run directly:

    ./run_tests.py                 # use the binary built by `make lsp`
    SAIL_LSP=/path/to/sail_lsp ./run_tests.py

Results are written to ``tests.xml`` in the JUnit format used by the other
Sail test suites, and a non-zero exit code is returned if anything fails.
"""

import datetime
import html
import os
import pathlib
import sys
import traceback

from lsp_harness import LspClient, Workspace, full_change, incremental_change


class color:
    NOTICE = "\033[94m"
    PASS = "\033[92m"
    FAIL = "\033[91m"
    END = "\033[0m"


HELLO = "default Order dec\n\nval main : unit -> unit\n\nfunction main() = ()\n"

# A file with multi-byte UTF-8 characters, to exercise the UTF-16 offset path.
UNICODE = "// π ≈ 3.14  — comment with wide chars\ndefault Order dec\n"

# A single-module project referencing m.sail; needed for the server to actually
# type-check a file and report diagnostics (without a project it stays idle).
PROJECT = "M {\n  files m.sail\n}\n"


# Dependency fixtures deliberately use a declaration in another file, so a
# stale file cache can be distinguished from a fresh successful check.
DEPENDENCY_PROJECT = "M {\n  files dependency.sail, m.sail\n}\n"
DEPENDENCY = "default Order dec\nval helper : int -> int\nfunction helper(x) = x\n"
BOOL_DEPENDENCY = "default Order dec\nval helper : bool -> bool\nfunction helper(x) = x\n"
DEPENDENT = "val use_helper : unit -> int\nfunction use_helper() = helper(4)\n"
BOOL_DEPENDENT = "val use_helper : unit -> bool\nfunction use_helper() = helper(true)\n"


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def diagnostics_uri(notification):
    check(
        notification.get("method") == "textDocument/publishDiagnostics",
        "expected publishDiagnostics, got {}".format(notification.get("method")),
    )
    return notification["params"]["uri"]


def write_workspace_file(ws, name, contents):
    with open(ws.path(name), "w", encoding="utf-8") as f:
        f.write(contents)


def watched_file(client, uri, change_type=2):
    client.notify("workspace/didChangeWatchedFiles", {"changes": [{"uri": uri, "type": change_type}]})


def document_diagnostics(client, uris):
    pending = set(uris)
    result = {}
    while pending:
        note = client.wait_notification("textDocument/publishDiagnostics")
        uri = diagnostics_uri(note)
        check(uri in pending, "unexpected or duplicate diagnostics for {}".format(uri))
        pending.remove(uri)
        result[uri] = note["params"]["diagnostics"]
    return result


def dependency_definition(client, uri, code=DEPENDENT):
    lines = code.splitlines()
    line = next(i for i, text in enumerate(lines) if "= helper(" in text)
    return client.definition(uri, line, lines[line].rindex("helper(") + 1)


# -- test cases --------------------------------------------------------------


def test_initialize():
    """initialize advertises the server name and document-sync capabilities."""
    with LspClient() as client:
        result = client.initialize()
        info = result.get("serverInfo", {})
        check(info.get("name") == "sail_lsp", "unexpected serverInfo: {}".format(info))

        sync = result["capabilities"]["textDocumentSync"]
        check(sync["openClose"] is True, "openClose not advertised: {}".format(sync))
        # 2 == TextDocumentSyncKind.Incremental
        check(sync["change"] == 2, "expected incremental sync, got {}".format(sync["change"]))
        check(bool(sync["save"]), "save not advertised: {}".format(sync))

        client.shutdown()
        client.exit()


def test_shutdown_exit():
    """A shutdown request returns null and exit terminates with code 0."""
    with LspClient() as client:
        client.initialize()
        result = client.shutdown()
        check(result is None, "shutdown should return null, got {}".format(result))
        client.exit(expected_code=0)


def test_did_change_publishes_diagnostics():
    """Editing an open document yields a publishDiagnostics for that document."""
    with Workspace({"m.sail": HELLO}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        client.did_open(ws.uri("m.sail"), HELLO)
        client.did_change(ws.uri("m.sail"), incremental_change(0, 0, 0, 0, "// edit\n"))
        notification = client.wait_notification("textDocument/publishDiagnostics")
        check(
            diagnostics_uri(notification) == ws.uri("m.sail"),
            "diagnostics for wrong uri: {}".format(diagnostics_uri(notification)),
        )
        client.shutdown()
        client.exit()


def test_did_save_publishes_diagnostics():
    """Saving an open document yields a publishDiagnostics for that document."""
    with Workspace({"m.sail": HELLO}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        client.did_open(ws.uri("m.sail"), HELLO)
        client.did_save(ws.uri("m.sail"))
        notification = client.wait_notification("textDocument/publishDiagnostics")
        check(diagnostics_uri(notification) == ws.uri("m.sail"), "diagnostics for wrong uri")
        client.shutdown()
        client.exit()


def test_incremental_edits():
    """A sequence of incremental edits keeps the server responsive."""
    with Workspace({"m.sail": HELLO}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, HELLO)

        edits = [
            incremental_change(0, 0, 0, 0, "// header\n"),   # insert a line at the top
            incremental_change(1, 0, 1, 0, "// second\n"),   # insert another line
            incremental_change(0, 0, 1, 0, ""),              # delete the first line
            full_change("default Order dec\n"),              # whole-document replace
        ]
        for version, change in enumerate(edits, start=2):
            client.did_change(uri, change, version=version)
            notification = client.wait_notification("textDocument/publishDiagnostics")
            check(diagnostics_uri(notification) == uri, "diagnostics for wrong uri")

        # Server is still healthy and responds to a request.
        check(client.shutdown() is None, "shutdown failed after edits")
        client.exit()


def test_unicode_offsets():
    """Edits expressed in UTF-16 offsets over multi-byte text don't crash the server."""
    with Workspace({"u.sail": UNICODE}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("u.sail")
        client.did_open(uri, UNICODE)
        # Insert after the multi-byte characters on line 0. LSP character
        # offsets are counted in UTF-16 code units, not bytes.
        client.did_change(uri, incremental_change(0, 12, 0, 12, "X"))
        notification = client.wait_notification("textDocument/publishDiagnostics")
        check(diagnostics_uri(notification) == uri, "diagnostics for wrong uri")
        client.shutdown()
        client.exit()


def test_open_close_reopen():
    """Closing then reopening a document leaves the server healthy."""
    with Workspace({"m.sail": HELLO}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, HELLO)
        # didOpen publishes diagnostics for the opened document; consume them.
        check(diagnostics_uri(client.wait_notification("textDocument/publishDiagnostics")) == uri,
              "diagnostics for wrong uri")
        client.did_close(uri)
        # didClose produces no notification of its own.
        client.expect_no_notification()
        client.did_open(uri, HELLO)
        client.did_change(uri, incremental_change(0, 0, 0, 0, "// again\n"))
        notification = client.wait_notification("textDocument/publishDiagnostics")
        check(diagnostics_uri(notification) == uri, "diagnostics for wrong uri")
        client.shutdown()
        client.exit()


def test_missing_file_does_not_crash():
    """Opening a non-existent document must not take the server down."""
    with LspClient() as client:
        client.initialize()
        client.initialized()
        # This path does not exist on disk; the server logs an error but must
        # keep serving requests.
        client.did_open("file:///no/such/sail/file.sail", "default Order dec\n")
        check(client.shutdown() is None, "server did not survive a bad didOpen")
        client.exit()


def decode_semantic_tokens(data, token_types):
    """Decode the LSP delta-encoded semantic token array into a list of
    (line, start_char, length, type_name) tuples, all zero-based and in UTF-16
    code units."""
    tokens = []
    line = 0
    char = 0
    for i in range(0, len(data), 5):
        delta_line, delta_start, length, type_index, _modifiers = data[i : i + 5]
        line += delta_line
        char = delta_start if delta_line else char + delta_start
        tokens.append((line, char, length, token_types[type_index]))
    return tokens


def semantic_tokens_legend(init_result):
    provider = init_result["capabilities"].get("semanticTokensProvider")
    check(provider is not None, "semanticTokensProvider not advertised")
    return provider


def test_semantic_tokens_capability():
    """The server advertises a semanticTokens provider with a full legend."""
    with LspClient(args=["--highlight"]) as client:
        provider = semantic_tokens_legend(client.initialize())
        check(provider.get("full") is True, "full semantic tokens not advertised: {}".format(provider))
        types = provider["legend"]["tokenTypes"]
        for expected in ("keyword", "comment", "string", "number"):
            check(expected in types, "legend missing {!r}: {}".format(expected, types))
        client.shutdown()
        client.exit()


def test_semantic_tokens_full():
    """semanticTokens/full lexes the buffer into typed, positioned tokens."""
    code = 'val x = 0xFF // hi\n"str"\n'
    with Workspace({"m.sail": code}) as ws, LspClient(args=["--highlight"]) as client:
        types = semantic_tokens_legend(client.initialize(ws.root_uri()))["legend"]["tokenTypes"]
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        result = client.semantic_tokens_full(uri)
        check(result is not None, "no semantic tokens returned")
        tokens = decode_semantic_tokens(result["data"], types)
        expected = [
            (0, 0, 3, "keyword"),  # val
            (0, 8, 4, "number"),  # 0xFF
            (0, 13, 5, "comment"),  # // hi
            (1, 0, 5, "string"),  # "str"
        ]
        for token in expected:
            check(token in tokens, "expected token {} not found in {}".format(token, tokens))
        client.shutdown()
        client.exit()


def test_semantic_tokens_unicode():
    """Token positions and lengths are reported in UTF-16 code units."""
    # The string literal "ππ" is 6 UTF-8 bytes but 4 UTF-16 code units.
    code = 'let x = "ππ"\n'
    with Workspace({"m.sail": code}) as ws, LspClient(args=["--highlight"]) as client:
        types = semantic_tokens_legend(client.initialize(ws.root_uri()))["legend"]["tokenTypes"]
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        tokens = decode_semantic_tokens(client.semantic_tokens_full(uri)["data"], types)
        check((0, 8, 4, "string") in tokens, "UTF-16 string token not found in {}".format(tokens))
        client.shutdown()
        client.exit()


def test_semantic_tokens_multiline():
    """A token spanning several lines is split into one token per line."""
    code = "/* a\n b */\nval x\n"
    with Workspace({"m.sail": code}) as ws, LspClient(args=["--highlight"]) as client:
        types = semantic_tokens_legend(client.initialize(ws.root_uri()))["legend"]["tokenTypes"]
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        tokens = decode_semantic_tokens(client.semantic_tokens_full(uri)["data"], types)
        # The block comment covers "/* a" on line 0 and " b */" on line 1.
        for token in [(0, 0, 4, "comment"), (1, 0, 5, "comment")]:
            check(token in tokens, "expected comment token {} not found in {}".format(token, tokens))
        client.shutdown()
        client.exit()


def test_folding_range_capability():
    """The server advertises a folding-range provider."""
    with LspClient(args=["--folding"]) as client:
        result = client.initialize()
        provider = result["capabilities"].get("foldingRangeProvider")
        check(provider is True, "foldingRangeProvider not advertised: {}".format(provider))
        client.shutdown()
        client.exit()


def test_folding_range():
    """foldingRange folds bracket pairs and multi-line block comments."""
    code = (
        "/* a block\n"        # 0  comment start
        "   comment */\n"     # 1  comment end
        "function main() = {\n"  # 2  '{' opens here
        "  let x = [1,\n"     # 3  '[' opens here
        "           2];\n"    # 4  ']' closes here
        "  ()\n"              # 5
        "}\n"                 # 6  '}' closes here
        "// tail\n"           # 7  line comment: not foldable
    )
    with Workspace({"m.sail": code}) as ws, LspClient(args=["--folding"]) as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        ranges = client.folding_range(uri)
        got = {(r["startLine"], r["endLine"], r.get("kind")) for r in ranges}
        expected = {
            (0, 1, "comment"),  # /* ... */
            (2, 6, "region"),   # { ... }
            (3, 4, "region"),   # [ ... ]
        }
        check(expected <= got, "expected folding ranges {} in {}".format(expected, got))
        # A single-line construct (the line comment) produces no fold.
        check(all(r["endLine"] > r["startLine"] for r in ranges), "single-line fold reported: {}".format(ranges))
        client.shutdown()
        client.exit()


def test_definition_capability():
    """The server advertises a definition provider."""
    with LspClient() as client:
        result = client.initialize()
        provider = result["capabilities"].get("definitionProvider")
        check(provider is True, "definitionProvider not advertised: {}".format(provider))
        client.shutdown()
        client.exit()


def test_definition():
    """go-to-definition on a call jumps to the callee's val definition."""
    code = (
        "default Order dec\n"                # 0
        "val foo : int -> int\n"             # 1  definition: 'foo' at chars 4-7
        "function foo(x) = x\n"              # 2
        "function main() -> int = foo(3)\n"  # 3  call: 'foo' at chars 25-27
    )
    with Workspace({"proj.sail_project": PROJECT, "m.sail": code}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        # Wait for the file to be type-checked so the AST is available.
        client.wait_notification("textDocument/publishDiagnostics")
        locations = client.definition(uri, 3, 26)
        check(locations, "no definition returned for call site")
        loc = locations[0]
        check(loc["uri"] == uri, "definition in wrong file: {}".format(loc["uri"]))
        start = loc["range"]["start"]
        check(start["line"] == 1, "expected definition on line 1 (the val), got {}".format(start))
        client.shutdown()
        client.exit()


def test_definition_for_each_open_document():
    """Navigation uses the requested document after another project is opened."""
    code = (
        "default Order dec\n"
        "val foo : int -> int\n"
        "function foo(x) = x\n"
        "function main() -> int = foo(3)\n"
    )
    files = {
        "a/proj.sail_project": PROJECT,
        "a/m.sail": code,
        "b/proj.sail_project": PROJECT,
        "b/m.sail": code,
    }
    with Workspace(files) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uris = [ws.uri("a/m.sail"), ws.uri("b/m.sail")]
        for uri in uris:
            client.did_open(uri, code)
            note = client.wait_notification("textDocument/publishDiagnostics")
            check(diagnostics_uri(note) == uri, "diagnostics for wrong uri")
            check(note["params"]["diagnostics"] == [], "initial project failed")
        for uri in uris:
            locations = client.definition(uri, 3, 26)
            check(locations and locations[0]["uri"] == uri, "navigation used another document's AST")
        client.shutdown()
        client.exit()


def test_definition_absent():
    """Requesting a definition where there is no identifier yields null."""
    code = "default Order dec\n"
    with Workspace({"proj.sail_project": PROJECT, "m.sail": code}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        client.wait_notification("textDocument/publishDiagnostics")
        check(client.definition(uri, 0, 0) is None, "expected null definition on a keyword")
        client.shutdown()
        client.exit()


def test_formatting_capability():
    """The server advertises a formatting provider."""
    with LspClient() as client:
        provider = client.initialize()["capabilities"].get("documentFormattingProvider")
        check(provider is True, "documentFormattingProvider not advertised: {}".format(provider))
        client.shutdown()
        client.exit()


def test_formatting():
    """Formatting a badly laid out document returns one whole-document edit."""
    code = "default   Order    dec\nval  main :  unit->unit\nfunction  main()  =  ()\n"
    with Workspace({"m.sail": code}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        edits = client.formatting(uri)
        check(len(edits) == 1, "expected a single whole-document edit, got {}".format(edits))
        edit = edits[0]
        start, end = edit["range"]["start"], edit["range"]["end"]
        check(start == {"line": 0, "character": 0}, "edit does not start at the top of the file: {}".format(start))
        # The document has a trailing newline, so its last line is line 3 and empty.
        check(end == {"line": 3, "character": 0}, "edit does not cover the whole file: {}".format(end))
        formatted = edit["newText"]
        check("val main : unit -> unit" in formatted, "run-together spacing not fixed: {!r}".format(formatted))

        # Formatting is idempotent: the formatted text needs no further edits.
        client.did_change(uri, full_change(formatted))
        client.wait_notification("textDocument/publishDiagnostics")
        check(client.formatting(uri) == [], "formatted document was not left alone")
        client.shutdown()
        client.exit()


def test_formatting_unicode():
    """The replaced range ends at the end of the buffer, in UTF-16 code units."""
    # The last line holds two multi-byte characters: 12 UTF-16 code units, 14 bytes.
    # It deliberately has no trailing newline, so the last line is not empty.
    code = 'default   Order dec\nlet x = "ππ"'
    with Workspace({"m.sail": code}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        edits = client.formatting(uri)
        check(len(edits) == 1, "expected a single whole-document edit, got {}".format(edits))
        end = edits[0]["range"]["end"]
        check(end == {"line": 1, "character": 12}, "end position is not in UTF-16 code units: {}".format(end))
        client.shutdown()
        client.exit()


def test_formatting_syntax_error():
    """A document that does not parse cannot be formatted, and says so."""
    code = "default Order dec\nfoo bar baz\n"
    with Workspace({"m.sail": code}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        error = client.formatting(uri, expect_error=True)
        check("m.sail" in error["message"], "error does not name the file: {}".format(error))
        check("line 2" in error["message"], "error does not locate the problem: {}".format(error))
        # The server must still be serving requests afterwards.
        check(client.shutdown() is None, "server did not survive a formatting failure")
        client.exit()


def test_range_formatting_capability():
    """The server advertises a range-formatting provider."""
    with LspClient() as client:
        provider = client.initialize()["capabilities"].get("documentRangeFormattingProvider")
        check(provider is True, "documentRangeFormattingProvider not advertised: {}".format(provider))
        client.shutdown()
        client.exit()


# Two badly spaced definitions, separated by a comment and blank lines that
# belong to no definition. The first line is already formatted.
RANGE_CODE = (
    "default Order dec\n"    # 0
    "\n"                     # 1
    "// a comment\n"         # 2
    "val  f : int -> int\n"  # 3
    "\n"                     # 4
    "val  g : int -> int\n"  # 5
)


def test_range_formatting():
    """Formatting a range reformats the definitions it touches, and nothing else."""
    with Workspace({"m.sail": RANGE_CODE}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, RANGE_CODE)

        # An empty range - a bare cursor - selects the definition it sits in.
        edits = client.range_formatting(uri, 5, 4, 5, 4)
        check(len(edits) == 1, "expected one edit for the definition at the cursor, got {}".format(edits))
        check(edits[0]["newText"] == "val g : int -> int", "definition not reformatted: {}".format(edits[0]))
        check(
            edits[0]["range"] == {"start": {"line": 5, "character": 0}, "end": {"line": 5, "character": 19}},
            "edit does not cover exactly the definition: {}".format(edits[0]["range"]),
        )

        # A selection spanning both definitions yields one edit each. The already
        # formatted first line is not among them: it needs no edit.
        edits = client.range_formatting(uri, 3, 0, 5, 19)
        check(
            [e["newText"] for e in edits] == ["val f : int -> int", "val g : int -> int"],
            "expected an edit per selected definition, got {}".format(edits),
        )
        check([e["range"]["start"]["line"] for e in edits] == [3, 5], "edits on the wrong lines: {}".format(edits))
        client.shutdown()
        client.exit()


def test_range_formatting_outside_definition():
    """A range touching no definition produces no edits."""
    with Workspace({"m.sail": RANGE_CODE}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, RANGE_CODE)
        for line, what in [(2, "a comment"), (4, "a blank line")]:
            edits = client.range_formatting(uri, line, 0, line, 0)
            check(edits == [], "expected no edits for {}, got {}".format(what, edits))
        client.shutdown()
        client.exit()


def test_range_formatting_multiline():
    """A definition spanning several lines is replaced whole, and its neighbour is untouched."""
    code = (
        "function  main()  = {\n"        # 0
        "let  x  =  1;   // trailing\n"  # 1
        "      ()\n"                     # 2
        "}\n"                            # 3
        "\n"                             # 4
        "val  g : int -> int\n"          # 5
    )
    with Workspace({"m.sail": code}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        edits = client.range_formatting(uri, 1, 2, 1, 2)
        check(len(edits) == 1, "expected one edit for the enclosing definition, got {}".format(edits))
        edit = edits[0]
        check(
            edit["range"] == {"start": {"line": 0, "character": 0}, "end": {"line": 3, "character": 1}},
            "edit does not cover the whole definition: {}".format(edit["range"]),
        )
        check(
            edit["newText"] == "function main() = {\n    let x = 1; // trailing\n    ()\n}",
            "definition not reformatted as expected: {!r}".format(edit["newText"]),
        )
        client.shutdown()
        client.exit()


def test_range_formatting_attributes():
    """A definition with an attribute or a doc comment is formatted along with it."""
    # Attributes, doc comments and `private` wrap the definition they are
    # attached to in another definition whose location spans only the wrapper,
    # so the extent of such a definition has to be stitched back together.
    code = (
        "$[attr]\n"                      # 0
        "val  f : int -> int\n"          # 1
        "\n"                             # 2
        "/*! documented */\n"            # 3
        "$[complete]\n"                  # 4
        "function  main()  = ()\n"       # 5
        "\n"                             # 6
        "private val  g : int -> int\n"  # 7
    )
    with Workspace({"m.sail": code}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)

        # Whether the cursor is on the attribute or on the definition it is
        # attached to, both are reformatted as one.
        for line, character in [(0, 0), (1, 4)]:
            edits = client.range_formatting(uri, line, character, line, character)
            check(len(edits) == 1, "expected one edit at {}:{}, got {}".format(line, character, edits))
            check(
                edits[0]["newText"] == "$[attr]\nval f : int -> int",
                "attribute and definition not reformatted together: {!r}".format(edits[0]["newText"]),
            )
            check(
                edits[0]["range"] == {"start": {"line": 0, "character": 0}, "end": {"line": 1, "character": 19}},
                "edit does not span the attribute and the definition: {}".format(edits[0]["range"]),
            )

        # A doc comment stacked on top of an attribute is covered too.
        edits = client.range_formatting(uri, 5, 4, 5, 4)
        check(len(edits) == 1, "expected one edit for the documented definition, got {}".format(edits))
        check(
            edits[0]["range"]["start"] == {"line": 3, "character": 0},
            "edit does not start at the doc comment: {}".format(edits[0]["range"]),
        )

        # `private` is the third wrapper of this kind.
        edits = client.range_formatting(uri, 7, 12, 7, 12)
        check(len(edits) == 1, "expected one edit for the private definition, got {}".format(edits))
        check(
            edits[0]["newText"] == "private val g : int -> int",
            "private definition not reformatted: {!r}".format(edits[0]["newText"]),
        )
        client.shutdown()
        client.exit()


def test_error_diagnostic():
    """A file with an error yields a diagnostic with a valid, correctly located range."""
    # The syntax error is on line 1 (zero-based); LSP positions are zero-based.
    code = "default Order dec\nfoo bar baz\n"
    with Workspace({"proj.sail_project": PROJECT, "m.sail": code}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        note = client.wait_notification("textDocument/publishDiagnostics")
        check(diagnostics_uri(note) == uri, "diagnostics for wrong uri")
        diags = note["params"]["diagnostics"]
        check(len(diags) >= 1, "expected at least one diagnostic, got {}".format(diags))
        d = diags[0]
        check(d.get("severity") == 1, "expected Error severity (1), got {}".format(d.get("severity")))
        check(d.get("source") == "sail", "expected source 'sail', got {}".format(d.get("source")))
        message = d.get("message")
        check(isinstance(message, str) and message.strip() != "", "expected a non-empty message, got {!r}".format(message))
        start, end = d["range"]["start"], d["range"]["end"]
        check(start["line"] == 1, "expected diagnostic on line 1, got {}".format(start))
        # A well-formed range: start no later than end, both zero-based.
        check(start["character"] >= 0 and (end["line"], end["character"]) >= (start["line"], start["character"]),
              "malformed range {}".format(d["range"]))
        client.shutdown()
        client.exit()


def test_valid_file_has_no_diagnostics():
    """A well-formed file under a project produces an empty diagnostics list."""
    code = "default Order dec\n"
    with Workspace({"proj.sail_project": PROJECT, "m.sail": code}) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        note = client.wait_notification("textDocument/publishDiagnostics")
        diags = note["params"]["diagnostics"]
        check(diags == [], "expected no diagnostics for a valid file, got {}".format(diags))
        client.shutdown()
        client.exit()


def test_watched_dependency_rechecks_all_documents():
    """A disk edit and repair refresh every open consumer of a dependency."""
    project = "M {\n  files dependency.sail, m.sail, n.sail\n}\n"
    other = DEPENDENT.replace("use_helper", "another_helper")
    files = {
        "proj.sail_project": project,
        "dependency.sail": DEPENDENCY,
        "m.sail": DEPENDENT,
        "n.sail": other,
    }
    with Workspace(files) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uris = [ws.uri("m.sail"), ws.uri("n.sail")]
        for uri, code in zip(uris, [DEPENDENT, other]):
            client.did_open(uri, code)
            check(document_diagnostics(client, [uri])[uri] == [], "initial consumer did not check")
        write_workspace_file(ws, "dependency.sail", BOOL_DEPENDENCY)
        watched_file(client, ws.uri("dependency.sail"))
        diags = document_diagnostics(client, uris)
        check(all(diags[uri] for uri in uris), "changed dependency was not checked by both consumers")
        write_workspace_file(ws, "dependency.sail", DEPENDENCY)
        watched_file(client, ws.uri("dependency.sail"))
        check(all(not ds for ds in document_diagnostics(client, uris).values()), "repair left stale diagnostics")
        client.shutdown()
        client.exit()


def test_saved_dependency_rechecks_dependents():
    """didSave refreshes other open files, without requiring a watcher event."""
    files = {
        "proj.sail_project": DEPENDENCY_PROJECT,
        "dependency.sail": DEPENDENCY,
        "m.sail": DEPENDENT,
    }
    with Workspace(files) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        main_uri, dep_uri = ws.uri("m.sail"), ws.uri("dependency.sail")
        for uri, code in [(main_uri, DEPENDENT), (dep_uri, DEPENDENCY)]:
            client.did_open(uri, code)
            document_diagnostics(client, [uri])
        client.did_change(dep_uri, full_change(BOOL_DEPENDENCY))
        document_diagnostics(client, [dep_uri])
        client.did_save(dep_uri)
        diags = document_diagnostics(client, [main_uri, dep_uri])
        check(diags[dep_uri] == [] and diags[main_uri], "save did not refresh dependent diagnostics")
        client.did_change(dep_uri, full_change(DEPENDENCY), version=3)
        document_diagnostics(client, [dep_uri])
        client.did_save(dep_uri)
        check(
            all(not ds for ds in document_diagnostics(client, [main_uri, dep_uri]).values()),
            "saved repair did not clear dependent diagnostics",
        )
        client.shutdown()
        client.exit()


def test_watched_dependency_preserves_unsaved_buffers():
    """Watchers preserve unsaved consumers and dependencies, even through aliases."""
    project = DEPENDENCY_PROJECT.replace("dependency.sail", '"./dependency.sail"')
    files = {
        "proj.sail_project": project,
        "dependency.sail": DEPENDENCY,
        "m.sail": DEPENDENT,
    }
    with Workspace(files) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        main_uri, dep_uri = ws.uri("m.sail"), ws.uri("dependency.sail")
        for uri, code in [(dep_uri, DEPENDENCY), (main_uri, DEPENDENT)]:
            client.did_open(uri, code)
            document_diagnostics(client, [uri])
        client.did_change(dep_uri, full_change(BOOL_DEPENDENCY))
        document_diagnostics(client, [dep_uri])
        client.did_change(main_uri, full_change(BOOL_DEPENDENT))
        diags = document_diagnostics(client, [main_uri])[main_uri]
        check(diags == [], "unsaved buffers did not check: {}".format(diags))
        write_workspace_file(ws, "dependency.sail", "not valid Sail\n")
        watched_file(client, dep_uri)
        check(
            all(not ds for ds in document_diagnostics(client, [main_uri, dep_uri]).values()),
            "disk edit replaced an unsaved buffer",
        )
        os.unlink(ws.path("dependency.sail"))
        watched_file(client, dep_uri, 3)
        check(
            all(not ds for ds in document_diagnostics(client, [main_uri, dep_uri]).values()),
            "disk deletion discarded an editor-owned buffer",
        )
        check(dependency_definition(client, main_uri, BOOL_DEPENDENT), "unsaved dependency lost navigation")
        client.did_close(dep_uri)
        check(document_diagnostics(client, [main_uri])[main_uri], "close retained the missing dependency's buffer")
        write_workspace_file(ws, "dependency.sail", BOOL_DEPENDENCY)
        watched_file(client, dep_uri, 1)
        check(document_diagnostics(client, [main_uri])[main_uri] == [], "restoration did not recover")
        client.shutdown()
        client.exit()


def test_deleted_dependency_clears_navigation_and_recovers():
    """A missing dependency reports failure and cannot serve its previous AST."""
    files = {
        "proj.sail_project": DEPENDENCY_PROJECT,
        "dependency.sail": DEPENDENCY,
        "m.sail": DEPENDENT,
    }
    with Workspace(files) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, DEPENDENT)
        document_diagnostics(client, [uri])
        check(dependency_definition(client, uri), "initial dependency had no definition")
        os.unlink(ws.path("dependency.sail"))
        watched_file(client, ws.uri("dependency.sail"), 3)
        check(document_diagnostics(client, [uri])[uri], "missing dependency produced no error")
        check(dependency_definition(client, uri) is None, "missing dependency served a stale definition")
        hover = client.request(
            "textDocument/hover",
            {"textDocument": {"uri": uri}, "position": {"line": 1, "character": 25}},
        )
        check(hover is None, "missing dependency served a stale hover")
        write_workspace_file(ws, "dependency.sail", DEPENDENCY)
        watched_file(client, ws.uri("dependency.sail"), 1)
        check(document_diagnostics(client, [uri])[uri] == [], "restored dependency still failed")
        locations = dependency_definition(client, uri)
        check(locations and locations[0]["uri"] == ws.uri("dependency.sail"), "restoration lost definition")
        client.shutdown()
        client.exit()


def test_watched_include_refreshes_definition_locations():
    """An included file's cached contents and definition positions are refreshed."""
    code = '$include "dependency.sail"\n' + DEPENDENT
    files = {
        "proj.sail_project": PROJECT,
        "dependency.sail": DEPENDENCY,
        "m.sail": code,
    }
    with Workspace(files) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri = ws.uri("m.sail")
        client.did_open(uri, code)
        check(document_diagnostics(client, [uri])[uri] == [], "initial include failed")
        write_workspace_file(ws, "dependency.sail", "// moved\n// down\n" + DEPENDENCY)
        watched_file(client, ws.uri("dependency.sail"))
        check(document_diagnostics(client, [uri])[uri] == [], "changed include failed")
        locations = dependency_definition(client, uri, code)
        check(
            locations and locations[0]["range"]["start"]["line"] == 3,
            "include definition retained its old location: {}".format(locations),
        )
        client.shutdown()
        client.exit()


def test_watched_project_file_refreshes_and_recovers():
    """Project membership and syntax changes are read again from disk."""
    files = {
        "proj.sail_project": DEPENDENCY_PROJECT,
        "dependency.sail": DEPENDENCY,
        "m.sail": DEPENDENT,
    }
    with Workspace(files) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uri, project_uri = ws.uri("m.sail"), ws.uri("proj.sail_project")
        client.did_open(uri, DEPENDENT)
        document_diagnostics(client, [uri])
        for project in [PROJECT, "M {\n"]:
            write_workspace_file(ws, "proj.sail_project", project)
            watched_file(client, project_uri)
            check(document_diagnostics(client, [uri])[uri], "bad project produced no error")
            check(dependency_definition(client, uri) is None, "bad project served a stale definition")
            write_workspace_file(ws, "proj.sail_project", DEPENDENCY_PROJECT)
            watched_file(client, project_uri)
            check(document_diagnostics(client, [uri])[uri] == [], "project repair did not recover")
        client.shutdown()
        client.exit()


def test_watched_failure_isolated_between_projects():
    """A broken project cannot discard a different project's diagnostics or AST."""
    files = {}
    for directory in ["a", "b"]:
        files[directory + "/proj.sail_project"] = DEPENDENCY_PROJECT
        files[directory + "/dependency.sail"] = DEPENDENCY
        files[directory + "/m.sail"] = DEPENDENT
    files["unrelated.sail"] = ""
    with Workspace(files) as ws, LspClient() as client:
        client.initialize(ws.root_uri())
        client.initialized()
        uris = [ws.uri("a/m.sail"), ws.uri("b/m.sail")]
        for uri in uris:
            client.did_open(uri, DEPENDENT)
            check(document_diagnostics(client, [uri])[uri] == [], "initial project failed")
        os.unlink(ws.path("a/dependency.sail"))
        watched_file(client, ws.uri("a/dependency.sail"), 3)
        diags = document_diagnostics(client, uris)
        check(diags[uris[0]] and diags[uris[1]] == [], "failure leaked between projects")
        check(dependency_definition(client, uris[0]) is None, "broken project retained navigation")
        locations = dependency_definition(client, uris[1])
        check(locations and locations[0]["uri"] == ws.uri("b/dependency.sail"), "other project lost navigation")
        write_workspace_file(ws, "a/dependency.sail", DEPENDENCY)
        watched_file(client, ws.uri("a/dependency.sail"), 1)
        check(all(not ds for ds in document_diagnostics(client, uris).values()), "project did not recover")
        for uri, directory in zip(uris, ["a", "b"]):
            locations = dependency_definition(client, uri)
            check(
                locations and locations[0]["uri"] == ws.uri(directory + "/dependency.sail"),
                "navigation used another project's AST",
            )
        os.unlink(ws.path("unrelated.sail"))
        watched_file(client, ws.uri("unrelated.sail"), 3)
        check(all(not ds for ds in document_diagnostics(client, uris).values()), "unrelated deletion caused errors")
        client.shutdown()
        client.exit()


def test_watched_symlink_does_not_replace_old_target():
    """Retargeting an alias cannot overwrite its previous target's cached bytes."""
    files = {
        "old.sail": DEPENDENCY,
        "new.sail": BOOL_DEPENDENCY,
        "a/proj.sail_project": "M {\n  files ../dependency.sail, m.sail\n}\n",
        "b/proj.sail_project": "M {\n  files ../old.sail, m.sail\n}\n",
        "a/m.sail": DEPENDENT,
        "b/m.sail": DEPENDENT,
    }
    with Workspace(files) as ws, LspClient() as client:
        alias = os.path.join(ws.dir, "dependency.sail")
        ws.paths["dependency.sail"] = alias
        os.symlink(ws.path("old.sail"), alias)
        # Preserve the alias spelling: Workspace.uri resolves symlinks.
        alias_uri = pathlib.Path(alias).as_uri()
        client.initialize(ws.root_uri())
        client.initialized()
        client.did_open(alias_uri, DEPENDENCY)
        document_diagnostics(client, [alias_uri])
        client.did_close(alias_uri)
        uris = [ws.uri("a/m.sail"), ws.uri("b/m.sail")]
        for uri in uris:
            client.did_open(uri, DEPENDENT)
            check(document_diagnostics(client, [uri])[uri] == [], "initial project failed")
        os.unlink(alias)
        os.symlink(ws.path("new.sail"), alias)
        watched_file(client, alias_uri)
        diags = document_diagnostics(client, uris)
        check(diags[uris[0]], "alias consumer did not see its new target")
        check(
            diags[uris[1]] == [],
            "retargeting the alias corrupted the old target's cache: {}".format(diags[uris[1]]),
        )
        client.shutdown()
        client.exit()


TESTS = [
    test_initialize,
    test_shutdown_exit,
    test_did_change_publishes_diagnostics,
    test_did_save_publishes_diagnostics,
    test_incremental_edits,
    test_unicode_offsets,
    test_open_close_reopen,
    test_missing_file_does_not_crash,
    test_semantic_tokens_capability,
    test_semantic_tokens_full,
    test_semantic_tokens_unicode,
    test_semantic_tokens_multiline,
    test_folding_range_capability,
    test_folding_range,
    test_definition_capability,
    test_definition,
    test_definition_for_each_open_document,
    test_definition_absent,
    test_formatting_capability,
    test_formatting,
    test_formatting_unicode,
    test_formatting_syntax_error,
    test_range_formatting_capability,
    test_range_formatting,
    test_range_formatting_outside_definition,
    test_range_formatting_multiline,
    test_range_formatting_attributes,
    test_error_diagnostic,
    test_valid_file_has_no_diagnostics,
    test_watched_dependency_rechecks_all_documents,
    test_saved_dependency_rechecks_dependents,
    test_watched_dependency_preserves_unsaved_buffers,
    test_deleted_dependency_clears_navigation_and_recovers,
    test_watched_include_refreshes_definition_locations,
    test_watched_project_file_refreshes_and_recovers,
    test_watched_failure_isolated_between_projects,
    test_watched_symlink_does_not_replace_old_target,
]


# -- runner ------------------------------------------------------------------


def main():
    only = sys.argv[1:]
    tests = [t for t in TESTS if not only or t.__name__ in only]

    passes = 0
    failures = 0
    xml = ""

    for test in tests:
        name = test.__name__
        label = "{} ".format(name).ljust(48, ".")
        try:
            test()
        except Exception as exc:
            failures += 1
            message = "{}: {}".format(type(exc).__name__, exc)
            print("{} {}FAIL{}".format(label, color.FAIL, color.END))
            print(traceback.format_exc())
            qmsg = html.escape(message)
            xml += '    <testcase name="{}">\n      <error message="{}">{}</error>\n    </testcase>\n'.format(
                name, qmsg, qmsg
            )
        else:
            passes += 1
            print("{} {}ok{}".format(label, color.PASS, color.END))
            xml += '    <testcase name="{}"/>\n'.format(name)

    print(
        "{}{} passes and {} failures{}".format(
            color.NOTICE, passes, failures, color.END
        )
    )

    timestamp = datetime.datetime.utcnow()
    suite = '<testsuites>\n  <testsuite name="lsp" tests="{}" failures="{}" timestamp="{}">\n{}  </testsuite>\n</testsuites>\n'
    with open(os.path.join(os.path.dirname(__file__), "tests.xml"), "w") as f:
        f.write(suite.format(passes + failures, failures, timestamp, xml))

    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
