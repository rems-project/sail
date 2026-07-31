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
    # Three checks: the marker is absent by default, SAIL_PLUGIN_DIR adds it
    # without losing any built-in plugin options, and SAIL_NO_PLUGINS still
    # overrides SAIL_PLUGIN_DIR.
    banner('Testing loading of external plugins from SAIL_PLUGIN_DIR in addition to native sail plugins')
    results = Results('plugins')

    if not ensure_dummy_plugin_built():
        print_skip('sail_plugin_dir')
        results._add_status('sail_plugin_dir', 'skipped', 'could not build the dummy plugin: {}'.format(dummy_cmxs))
        return results

    with tempfile.TemporaryDirectory() as custom_dir:
        shutil.copy(dummy_cmxs, custom_dir)
        if os.path.exists(dummy_cma):
            shutil.copy(dummy_cma, custom_dir)

        baseline = sail_help(clean_env())
        with_plugin_dir = sail_help(clean_env(SAIL_PLUGIN_DIR=custom_dir))
        with_no_plugins = sail_help(clean_env(SAIL_PLUGIN_DIR=custom_dir, SAIL_NO_PLUGINS='1'))

    # The marker must not appear without SAIL_PLUGIN_DIR, otherwise its presence
    # below wouldn't actually show that SAIL_PLUGIN_DIR was scanned
    if marker not in baseline:
        results.passes += 1
        results.xml += '    <testcase name="sail_plugin_dir_marker_absent_by_default"/>\n'
        print_ok('sail_plugin_dir_marker_absent_by_default')
    else:
        msg = 'marker {} unexpectedly present without SAIL_PLUGIN_DIR'.format(marker)
        results._add_failure('sail_plugin_dir_marker_absent_by_default', msg)
        print('{}Failed{}: sail_plugin_dir_marker_absent_by_default: {}'.format(color.FAIL, color.END, msg))

    # SAIL_PLUGIN_DIR should add the marker without losing any built-in options
    lost = sorted(flag for flag in baseline - with_plugin_dir if flag.startswith('-'))
    if not lost and marker in with_plugin_dir:
        results.passes += 1
        results.xml += '    <testcase name="sail_plugin_dir_adds_builtins"/>\n'
        print_ok('sail_plugin_dir_adds_builtins')
    else:
        msg = 'lost built-in flags {}, marker present: {}'.format(lost, marker in with_plugin_dir)
        results._add_failure('sail_plugin_dir_adds_builtins', msg)
        print('{}Failed{}: sail_plugin_dir_adds_builtins: {}'.format(color.FAIL, color.END, msg))

    # SAIL_NO_PLUGINS should still take precedence over SAIL_PLUGIN_DIR
    if marker not in with_no_plugins:
        results.passes += 1
        results.xml += '    <testcase name="sail_no_plugins_overrides_plugin_dir"/>\n'
        print_ok('sail_no_plugins_overrides_plugin_dir')
    else:
        msg = 'marker {} present despite SAIL_NO_PLUGINS'.format(marker)
        results._add_failure('sail_no_plugins_overrides_plugin_dir', msg)
        print('{}Failed{}: sail_no_plugins_overrides_plugin_dir: {}'.format(color.FAIL, color.END, msg))

    return results


results = test_plugin_dir_include_extra_plugin()

xml = '<testsuites>\n' + results.finish() + '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()

sys.exit(1 if results.failures else 0)
