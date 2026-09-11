#!/usr/bin/env python3

"""Regression tests for Sail's plugin loading (the SAIL_PLUGIN_DIR environment
variable, see get_plugin_dir() in src/bin/sail.ml).

Run directly:
    dune build --release            # or: make sail
    SAIL_DIR="$(pwd)" SAIL="$(pwd)/sail" test/plugins/run_tests.py
"""

import os
import shutil
import subprocess
import sys
import tempfile

os.chdir(os.path.dirname(__file__))

# add `test/` to Python's module search path to allow finding `sailtest`
sys.path.insert(0, os.path.realpath('..'))
from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()

print('Sail exe at {}'.format(sail))
print('Sail dir at {}'.format(sail_dir))

# A plugin built only for this test (no `install` stanza, so `opam install`
# never builds it as a side effect of installing the sail package itself).
repo_root = os.path.realpath(os.path.join('..', '..'))
dummy_plugin_dir = os.path.join(repo_root, '_build', 'default', 'test', 'plugins', 'dummy_plugin')
dummy_cmxs = os.path.join(dummy_plugin_dir, 'sail_plugin_dir_test.cmxs')
dummy_cma = os.path.join(dummy_plugin_dir, 'sail_plugin_dir_test.cma')
marker = '--sail-plugin-dir-test-marker'

# One of the flags added by a real built-in plugin (the smt backend), used to
# check whether the built-in plugin directory was scanned or not
builtin_flag = '--smt-auto'

# `sail_dir` (e.g. <prefix>/share/sail) and the built-in plugin directory
# (<prefix>/share/libsail/plugins) are siblings under the same install prefix
default_plugin_dir = os.path.join(os.path.dirname(sail_dir), 'libsail', 'plugins')


def ensure_dummy_plugin_built():
    if os.path.exists(dummy_cmxs):
        return True
    try:
        subprocess.run(
            ['dune', 'build', 'test/plugins/dummy_plugin/sail_plugin_dir_test.cmxs'],
            cwd=repo_root,
            capture_output=True,
        )
    except FileNotFoundError:
        return False  # no dune available here, so this really can't be tested
    return os.path.exists(dummy_cmxs)


def sail_help(env):
    p = subprocess.run([sail, '--help'], capture_output=True, text=True, env=env)
    if p.returncode != 0:
        sys.exit('sail --help exited with status {}: {}'.format(p.returncode, p.stderr))
    # --help prints its usage message (including plugin-provided options) to stderr
    return set((p.stdout + p.stderr).split())


def clean_env(**extra):
    env = dict(os.environ)
    env.pop('SAIL_NO_PLUGINS', None)
    env.pop('SAIL_PLUGIN_DIR', None)
    env.update(extra)
    return env


def test_plugin_dir_include_extra_plugin():
    # Checks: the marker is absent by default, SAIL_NO_PLUGINS drops the
    # built-in plugins, SAIL_PLUGIN_DIR replaces the built-in plugin
    # directory rather than adding to it, and SAIL_PLUGIN_DIR is treated as a
    # colon-separated list of directories.
    banner('Testing loading of external plugins from SAIL_PLUGIN_DIR instead of native sail plugins')
    results = Results('plugins')

    def check(name, condition, detail):
        if condition:
            results.passes += 1
            results.xml += '    <testcase name="{}"/>\n'.format(name)
            print_ok(name)
        else:
            results._add_failure(name, detail)
            print('{}Failed{}: {}: {}'.format(color.FAIL, color.END, name, detail))

    if not ensure_dummy_plugin_built():
        print_skip('sail_plugin_dir')
        results._add_status('sail_plugin_dir', 'skipped', 'could not build the dummy plugin: {}'.format(dummy_cmxs))
        return results

    if not os.path.isdir(default_plugin_dir):
        print_skip('sail_plugin_dir')
        results._add_status(
            'sail_plugin_dir', 'skipped', 'could not find the built-in plugin directory: {}'.format(default_plugin_dir)
        )
        return results

    with tempfile.TemporaryDirectory() as custom_dir:
        shutil.copy(dummy_cmxs, custom_dir)
        if os.path.exists(dummy_cma):
            shutil.copy(dummy_cma, custom_dir)

        baseline = sail_help(clean_env())
        with_no_plugins = sail_help(clean_env(SAIL_NO_PLUGINS='1'))
        with_plugin_dir = sail_help(clean_env(SAIL_PLUGIN_DIR=custom_dir))
        with_no_plugins_and_plugin_dir = sail_help(clean_env(SAIL_NO_PLUGINS='1', SAIL_PLUGIN_DIR=custom_dir))
        with_colon_separated_dirs = sail_help(
            clean_env(SAIL_PLUGIN_DIR='{}:{}'.format(custom_dir, default_plugin_dir))
        )

    # The marker must not appear without SAIL_PLUGIN_DIR, otherwise its presence
    # below wouldn't actually show that SAIL_PLUGIN_DIR was scanned
    check(
        'sail_plugin_dir_marker_absent_by_default',
        marker not in baseline,
        'marker {} unexpectedly present without SAIL_PLUGIN_DIR'.format(marker),
    )

    # Sanity check for the tests below that rely on this flag: it is present
    # by default...
    check(
        'sail_plugin_dir_builtin_present_by_default',
        builtin_flag in baseline,
        'built-in flag {} missing without SAIL_NO_PLUGINS'.format(builtin_flag),
    )

    # ...and dropped when SAIL_NO_PLUGINS is set
    check(
        'sail_no_plugins_drops_builtins',
        builtin_flag not in with_no_plugins,
        'built-in flag {} still present with SAIL_NO_PLUGINS'.format(builtin_flag),
    )

    # SAIL_NO_PLUGINS should take precedence over SAIL_PLUGIN_DIR, not just the built-in directory
    check(
        'sail_no_plugins_overrides_plugin_dir',
        marker not in with_no_plugins_and_plugin_dir,
        'marker {} present despite SAIL_NO_PLUGINS'.format(marker),
    )

    # SAIL_PLUGIN_DIR should load the marker plugin, and no longer load the
    # built-in plugin directory (so the built-in flags disappear)
    check(
        'sail_plugin_dir_replaces_builtins',
        marker in with_plugin_dir and builtin_flag not in with_plugin_dir,
        'marker present: {}, built-in flag {} present: {}'.format(
            marker in with_plugin_dir, builtin_flag, builtin_flag in with_plugin_dir
        ),
    )

    # SAIL_PLUGIN_DIR should be treated as a colon-separated list of
    # directories, all of which are scanned for plugins
    check(
        'sail_plugin_dir_colon_separated_list',
        marker in with_colon_separated_dirs and builtin_flag in with_colon_separated_dirs,
        'marker present: {}, built-in flag {} present: {}'.format(
            marker in with_colon_separated_dirs, builtin_flag, builtin_flag in with_colon_separated_dirs
        ),
    )

    return results


results = test_plugin_dir_include_extra_plugin()

xml = '<testsuites>\n' + results.finish() + '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()

sys.exit(1 if results.failures else 0)
