#!/usr/bin/env python3

import os
import re
import sys
import hashlib
import argparse

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

update_expected = args.update_expected

sail_dir = get_sail_dir()
sail = get_sail()

# Self-tests refers to self contained Sail programs in test/c/ which are Sail programs
# that you can run to exercise the language and the extracted output.
# Not all self-tests are supported.
# TODO: once we support many of those, we should make this a `skip_selftests`
include_selftests = {
    'hello_world.sail',
}

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_lean(subdir: str, allowed_list = None, runnable: bool = False):
    """
    Run all Sail files available in the `subdir`.
    If `runnable` is set to `True`, it will do `lake run`
    instead of `lake build`.
    """
    banner(f'Testing lean target (sub-directory: {subdir})')
    results = Results(subdir)
    for filenames in chunks(os.listdir(f'../{subdir}'), parallel()):
        tests = {}
        for filename in filenames:
            if allowed_list is not None and filename not in allowed_list:
                continue

            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                os.chdir(f'../{subdir}')
                step('rm -r {} || true'.format(basename))
                step('mkdir -p {}'.format(basename))
                # TODO: should probably be dependent on whether print should be pure or effectful.
                extra_flags = ' '.join([
                    '--splice',
                    'coq-print.splice'
                ] if runnable else [ ])
                step('\'{}\' {} {} --lean --lean-output-dir {}'.format(sail, extra_flags, filename, basename))
                if runnable:
                    step(f'lake exe run > expected 2> err_status', cwd=f'{basename}/out')
                else:
                    # NOTE: lake --dir does not behave the same as cd $dir && lake build...
                    step('lake build', cwd=f'{basename}/out')

                status = step_with_status(f'diff {basename}/out/Out.lean {basename}.expected.lean')
                if status != 0:
                    if update_expected:
                        print(f'Overriding file {basename}.expected.lean')
                        step(f'cp {basename}/out/Out.lean {basename}.expected.lean')
                    else:
                        sys.exit(1)

                if runnable:
                    status = step_with_status(f'diff {basename}/out/expected {basename}.expect')
                    if status != 0:
                        sys.exit(1)
                step('rm -r {}'.format(basename))
                print_ok(filename)
                sys.exit(0)
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_lean('lean')
xml += test_lean('c', allowed_list=include_selftests, runnable=True)

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
