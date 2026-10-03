"""Regression tests for Sail's plugin loading (the SAIL_PLUGIN_DIR environment
variable, see get_plugin_dir() in src/bin/sail.ml).

Run with:
    dune build --release            # or: make sail
    SAIL_DIR="$(pwd)" SAIL="$(pwd)/sail" test/suites/runner.py -s plugins
"""

import os
import shutil
import subprocess
import sys
import tempfile

from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "plugins")

# A plugin built only for this test (no `install` stanza, so `opam install`
# never builds it as a side effect of installing the sail package itself).
_REPO_ROOT = os.path.realpath(os.path.join(TEST_DIR, ".."))
_DUMMY_PLUGIN_DIR = os.path.join(
    _REPO_ROOT, "_build", "default", "test", "plugins", "dummy_plugin"
)
_DUMMY_CMXS = os.path.join(_DUMMY_PLUGIN_DIR, "sail_plugin_dir_test.cmxs")
_DUMMY_CMA = os.path.join(_DUMMY_PLUGIN_DIR, "sail_plugin_dir_test.cma")
_MARKER = "--sail-plugin-dir-test-marker"

# One of the flags added by a real built-in plugin (the smt backend), used to
# check whether the built-in plugin directory was scanned or not
_BUILTIN_FLAG = "--smt-auto"


def ensure_dummy_plugin_built():
    if os.path.exists(_DUMMY_CMXS):
        return True
    try:
        subprocess.run(
            ["dune", "build", "test/plugins/dummy_plugin/sail_plugin_dir_test.cmxs"],
            cwd=_REPO_ROOT,
            capture_output=True,
        )
    except FileNotFoundError:
        return False  # no dune available here, so this really can't be tested
    return os.path.exists(_DUMMY_CMXS)


def clean_env(**extra):
    env = dict(os.environ)
    env.pop("SAIL_NO_PLUGINS", None)
    env.pop("SAIL_PLUGIN_DIR", None)
    env.update(extra)
    return env


@suite("plugins", _SUITE_DIR)
class PluginTests(SailTest):
    fail_on_error = True

    def run(self):
        # Checks: the marker is absent by default, SAIL_NO_PLUGINS drops the
        # built-in plugins, SAIL_PLUGIN_DIR replaces the built-in plugin
        # directory rather than adding to it, and SAIL_PLUGIN_DIR is treated as a
        # colon-separated list of directories.
        self.banner(
            "Testing loading of external plugins from SAIL_PLUGIN_DIR instead of native sail plugins"
        )
        results = Results("plugins")
        self._run_checks(results)
        self.add_results(results)

    def _sail_help(self, env):
        p = subprocess.run(
            [self.sail, "--help"], capture_output=True, text=True, env=env
        )
        if p.returncode != 0:
            sys.exit(f"sail --help exited with status {p.returncode}: {p.stderr}")
        # --help prints its usage message (including plugin-provided options) to stderr
        return set((p.stdout + p.stderr).split())

    def _run_checks(self, results):
        def check(name, condition, detail):
            if condition:
                results.add_pass(name)
                self._print_ok(name)
            else:
                results.add_failure(name, detail)
                print(f"{Color.FAIL}Failed{Color.END}: {name}: {detail}")

        # `sail_dir` (e.g. <prefix>/share/sail) and the built-in plugin directory
        # (<prefix>/share/libsail/plugins) are siblings under the same install prefix
        default_plugin_dir = os.path.join(
            os.path.dirname(self.sail_dir), "libsail", "plugins"
        )

        if not ensure_dummy_plugin_built():
            self._print_skip("sail_plugin_dir")
            results.add_skip(
                "sail_plugin_dir", f"could not build the dummy plugin: {_DUMMY_CMXS}"
            )
            return

        if not os.path.isdir(default_plugin_dir):
            self._print_skip("sail_plugin_dir")
            results.add_skip(
                "sail_plugin_dir",
                f"could not find the built-in plugin directory: {default_plugin_dir}",
            )
            return

        with tempfile.TemporaryDirectory() as custom_dir:
            shutil.copy(_DUMMY_CMXS, custom_dir)
            if os.path.exists(_DUMMY_CMA):
                shutil.copy(_DUMMY_CMA, custom_dir)

            baseline = self._sail_help(clean_env())
            with_no_plugins = self._sail_help(clean_env(SAIL_NO_PLUGINS="1"))
            with_plugin_dir = self._sail_help(clean_env(SAIL_PLUGIN_DIR=custom_dir))
            with_no_plugins_and_plugin_dir = self._sail_help(
                clean_env(SAIL_NO_PLUGINS="1", SAIL_PLUGIN_DIR=custom_dir)
            )
            with_colon_separated_dirs = self._sail_help(
                clean_env(SAIL_PLUGIN_DIR=f"{custom_dir}:{default_plugin_dir}")
            )

        # The marker must not appear without SAIL_PLUGIN_DIR, otherwise its presence
        # below wouldn't actually show that SAIL_PLUGIN_DIR was scanned
        check(
            "sail_plugin_dir_marker_absent_by_default",
            _MARKER not in baseline,
            f"marker {_MARKER} unexpectedly present without SAIL_PLUGIN_DIR",
        )

        # Sanity check for the tests below that rely on this flag: it is present
        # by default...
        check(
            "sail_plugin_dir_builtin_present_by_default",
            _BUILTIN_FLAG in baseline,
            f"built-in flag {_BUILTIN_FLAG} missing without SAIL_NO_PLUGINS",
        )

        # ...and dropped when SAIL_NO_PLUGINS is set
        check(
            "sail_no_plugins_drops_builtins",
            _BUILTIN_FLAG not in with_no_plugins,
            f"built-in flag {_BUILTIN_FLAG} still present with SAIL_NO_PLUGINS",
        )

        # SAIL_NO_PLUGINS should take precedence over SAIL_PLUGIN_DIR, not just the built-in directory
        check(
            "sail_no_plugins_overrides_plugin_dir",
            _MARKER not in with_no_plugins_and_plugin_dir,
            f"marker {_MARKER} present despite SAIL_NO_PLUGINS",
        )

        # SAIL_PLUGIN_DIR should load the marker plugin, and no longer load the
        # built-in plugin directory (so the built-in flags disappear)
        check(
            "sail_plugin_dir_replaces_builtins",
            _MARKER in with_plugin_dir and _BUILTIN_FLAG not in with_plugin_dir,
            f"marker present: {_MARKER in with_plugin_dir}, "
            f"built-in flag {_BUILTIN_FLAG} present: {_BUILTIN_FLAG in with_plugin_dir}",
        )

        # SAIL_PLUGIN_DIR should be treated as a colon-separated list of
        # directories, all of which are scanned for plugins
        check(
            "sail_plugin_dir_colon_separated_list",
            _MARKER in with_colon_separated_dirs
            and _BUILTIN_FLAG in with_colon_separated_dirs,
            f"marker present: {_MARKER in with_colon_separated_dirs}, "
            f"built-in flag {_BUILTIN_FLAG} present: {_BUILTIN_FLAG in with_colon_separated_dirs}",
        )
