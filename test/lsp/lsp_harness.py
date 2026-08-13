"""A minimal Language Server Protocol client for driving the Sail LSP server.

The server (``sail_lsp``) speaks JSON-RPC 2.0 over stdin/stdout using the
standard LSP ``Content-Length`` framing.  This module spawns the server as a
subprocess and provides just enough of a client to write black-box tests
against it:

  * request / notify with automatic framing,
  * a background reader thread that separates responses from notifications,
  * helpers for the document lifecycle (didOpen / didChange / ...),
  * discovery of the server binary via the ``SAIL_LSP`` environment variable.

The Sail server canonicalises paths with ``realpath`` when a document is
opened, so documents passed to :meth:`LspClient.did_open` must refer to files
that actually exist on disk.  Use :func:`workspace` to create throwaway files.
"""

import json
import os
import pathlib
import queue
import shutil
import subprocess
import tempfile
import threading


def find_server():
    """Locate the sail_lsp binary.

    Preference order: the ``SAIL_LSP`` environment variable, then the binary
    produced by ``make lsp`` in the source tree, then ``sail_lsp`` on PATH.
    """
    env = os.environ.get("SAIL_LSP")
    if env:
        return env

    here = os.path.dirname(os.path.realpath(__file__))
    built = os.path.realpath(os.path.join(here, "..", "..", "src", "sail_lsp", "_build", "default", "sail_lsp.exe"))
    if os.path.exists(built):
        return built

    return "sail_lsp"


def uri_of_path(path):
    return pathlib.Path(path).resolve().as_uri()


class Workspace:
    """A temporary directory of Sail source files, cleaned up on exit."""

    def __init__(self, files):
        self.dir = tempfile.mkdtemp(prefix="sail_lsp_test_")
        self.paths = {}
        for name, contents in files.items():
            path = os.path.join(self.dir, name)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                f.write(contents)
            self.paths[name] = path

    def path(self, name):
        return self.paths[name]

    def uri(self, name):
        return uri_of_path(self.paths[name])

    def root_uri(self):
        return uri_of_path(self.dir)

    def cleanup(self):
        shutil.rmtree(self.dir, ignore_errors=True)

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.cleanup()


class LspError(Exception):
    pass


class LspClient:
    """Drives a sail_lsp subprocess over stdio."""

    def __init__(self, server=None, timeout=15.0, args=None):
        """Spawn the server. ``args`` are extra command line flags, appended
        after ``--stdio``; features that are off by default (``--highlight``,
        ``--folding``) have to be enabled that way."""
        self.server = server or find_server()
        self.timeout = timeout
        self._next_id = 0
        self._responses = queue.Queue()
        self._notifications = queue.Queue()
        self._stderr_lines = []
        self._proc = subprocess.Popen(
            [self.server, "--stdio"] + list(args or []),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self._reader = threading.Thread(target=self._read_loop, daemon=True)
        self._reader.start()
        self._stderr_reader = threading.Thread(target=self._stderr_loop, daemon=True)
        self._stderr_reader.start()

    # -- low level IO --------------------------------------------------------

    def _read_loop(self):
        out = self._proc.stdout
        try:
            while True:
                headers = {}
                while True:
                    line = out.readline()
                    if not line:
                        raise EOFError
                    line = line.decode("utf-8").rstrip("\r\n")
                    if line == "":
                        break
                    key, _, value = line.partition(":")
                    headers[key.strip().lower()] = value.strip()
                length = int(headers["content-length"])
                body = out.read(length)
                message = json.loads(body.decode("utf-8"))
                if "id" in message and ("result" in message or "error" in message):
                    self._responses.put(message)
                elif "method" in message:
                    self._notifications.put(message)
                # else: server->client responses we didn't send; ignore.
        except (EOFError, ValueError, KeyError):
            # Stream closed (server exited), a truncated read, or a malformed
            # frame; wake up any waiters with a sentinel so they don't block.
            self._responses.put(None)
            self._notifications.put(None)

    def _stderr_loop(self):
        for line in iter(self._proc.stderr.readline, b""):
            self._stderr_lines.append(line.decode("utf-8", "replace").rstrip())

    def _send(self, message):
        body = json.dumps(message).encode("utf-8")
        header = "Content-Length: {}\r\n\r\n".format(len(body)).encode("ascii")
        self._proc.stdin.write(header + body)
        self._proc.stdin.flush()

    # -- public API ----------------------------------------------------------

    def notify(self, method, params=None):
        self._send({"jsonrpc": "2.0", "method": method, "params": params or {}})

    def request(self, method, params=None, expect_error=False):
        """Send a request and return its result. With ``expect_error`` the
        request must fail, and the JSON-RPC error object is returned instead."""
        self._next_id += 1
        request_id = self._next_id
        self._send({"jsonrpc": "2.0", "id": request_id, "method": method, "params": params or {}})
        try:
            response = self._responses.get(timeout=self.timeout)
        except queue.Empty:
            raise LspError("timed out waiting for response to {!r}\n{}".format(method, self.stderr()))
        if response is None:
            raise LspError("server exited while waiting for response to {!r}\n{}".format(method, self.stderr()))
        if response.get("id") != request_id:
            raise LspError("response id {} did not match request id {}".format(response.get("id"), request_id))
        if expect_error:
            if "error" not in response:
                raise LspError("request {!r} unexpectedly succeeded: {}".format(method, response.get("result")))
            return response["error"]
        if "error" in response:
            raise LspError("request {!r} returned error: {}".format(method, response["error"]))
        return response.get("result")

    def wait_notification(self, method=None, timeout=None):
        """Return the next notification, optionally waiting for a given method."""
        deadline_timeout = self.timeout if timeout is None else timeout
        while True:
            try:
                notification = self._notifications.get(timeout=deadline_timeout)
            except queue.Empty:
                raise LspError(
                    "timed out waiting for notification {!r}\n{}".format(method, self.stderr())
                )
            if notification is None:
                raise LspError(
                    "server exited while waiting for notification {!r}\n{}".format(method, self.stderr())
                )
            if method is None or notification.get("method") == method:
                return notification

    def expect_no_notification(self, timeout=0.5):
        """Assert that no notification arrives within the given window."""
        try:
            notification = self._notifications.get(timeout=timeout)
        except queue.Empty:
            return
        if notification is None:
            return
        raise LspError("unexpected notification: {}".format(json.dumps(notification)))

    # -- lifecycle helpers ---------------------------------------------------

    def initialize(self, root_uri=None):
        return self.request(
            "initialize",
            {"processId": os.getpid(), "rootUri": root_uri, "capabilities": {}},
        )

    def initialized(self):
        self.notify("initialized", {})

    def did_open(self, uri, text, language_id="sail", version=1):
        self.notify(
            "textDocument/didOpen",
            {"textDocument": {"uri": uri, "languageId": language_id, "version": version, "text": text}},
        )

    def did_change(self, uri, changes, version=2):
        self.notify(
            "textDocument/didChange",
            {"textDocument": {"uri": uri, "version": version}, "contentChanges": changes},
        )

    def did_save(self, uri):
        self.notify("textDocument/didSave", {"textDocument": {"uri": uri}})

    def did_close(self, uri):
        self.notify("textDocument/didClose", {"textDocument": {"uri": uri}})

    def semantic_tokens_full(self, uri):
        return self.request("textDocument/semanticTokens/full", {"textDocument": {"uri": uri}})

    def folding_range(self, uri):
        return self.request("textDocument/foldingRange", {"textDocument": {"uri": uri}})

    def formatting(self, uri, tab_size=4, insert_spaces=True, expect_error=False):
        return self.request(
            "textDocument/formatting",
            {"textDocument": {"uri": uri}, "options": {"tabSize": tab_size, "insertSpaces": insert_spaces}},
            expect_error=expect_error,
        )

    def range_formatting(self, uri, start_line, start_char, end_line, end_char, tab_size=4, expect_error=False):
        return self.request(
            "textDocument/rangeFormatting",
            {
                "textDocument": {"uri": uri},
                "range": {
                    "start": {"line": start_line, "character": start_char},
                    "end": {"line": end_line, "character": end_char},
                },
                "options": {"tabSize": tab_size, "insertSpaces": True},
            },
            expect_error=expect_error,
        )

    def definition(self, uri, line, character):
        return self.request(
            "textDocument/definition",
            {"textDocument": {"uri": uri}, "position": {"line": line, "character": character}},
        )

    def shutdown(self):
        return self.request("shutdown")

    def exit(self, expected_code=0, timeout=None):
        self.notify("exit")
        code = self.wait_for_exit(timeout=timeout)
        if expected_code is not None and code != expected_code:
            raise LspError("server exited with code {}, expected {}".format(code, expected_code))
        return code

    def wait_for_exit(self, timeout=None):
        try:
            return self._proc.wait(timeout=self.timeout if timeout is None else timeout)
        except subprocess.TimeoutExpired:
            raise LspError("server did not exit\n{}".format(self.stderr()))

    def stderr(self):
        return "\n".join(self._stderr_lines)

    def close(self):
        if self._proc.poll() is None:
            self._proc.kill()
            try:
                self._proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


def full_change(text):
    """A whole-document content change (no range)."""
    return [{"text": text}]


def incremental_change(start_line, start_char, end_line, end_char, text):
    """A ranged (incremental) content change using LSP line/UTF-16 offsets."""
    return [
        {
            "range": {
                "start": {"line": start_line, "character": start_char},
                "end": {"line": end_line, "character": end_char},
            },
            "text": text,
        }
    ]
