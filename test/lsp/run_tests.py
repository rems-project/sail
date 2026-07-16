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


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def diagnostics_uri(notification):
    check(
        notification.get("method") == "textDocument/publishDiagnostics",
        "expected publishDiagnostics, got {}".format(notification.get("method")),
    )
    return notification["params"]["uri"]


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
    with LspClient() as client:
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
    with Workspace({"m.sail": code}) as ws, LspClient() as client:
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
    with Workspace({"m.sail": code}) as ws, LspClient() as client:
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
    with Workspace({"m.sail": code}) as ws, LspClient() as client:
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
    with LspClient() as client:
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
    with Workspace({"m.sail": code}) as ws, LspClient() as client:
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
    test_definition_absent,
    test_error_diagnostic,
    test_valid_file_has_no_diagnostics,
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
