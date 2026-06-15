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
run_skips = args.run_skips
local_support_lib = args.lean_local_support_library

sail_dir = get_sail_dir()
sail = get_sail()

# Self-tests refers to self contained Sail programs in test/c/ which are Sail programs
# that you can run to exercise the language and the extracted output.
# Not all self-tests are supported.
skip_selftests = {
    'outcome_impl', # custom outcome types (not expected to work)
    'outcome_impl_int', # custom outcome types (not expected to work)
    'outcome_impl_bool', # custom outcome types (not expected to work)
    'union_variant_names',
    'varswap',
    'real',
    'poly_outcome',
    'string_of_bits',
    'pointer_assign',
    'concurrency_interface',
    'for_shadow',
    'string_literal_type',
    'issue429',
    'pc_no_wildcard',
    'type_if_bits',
    'nexp_simp_euclidian',
    'issue136',
    'anf_as_pattern',
    'real_prop',
    'constructor247',
    'deep_poly_nest',
    'config_abstract_bool', # Register type unsupported in state.ml
    'newtype',
    'concurrency_interface_v2',
    'concurrency_interface_v2_var',
    'config_map_guard',
    'let_assert',
    'tuple_tuple_lexp',
}

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def get_support_lib(subdir) -> str:
    if local_support_lib:
        return local_support_lib
    else:
        lean_path = f"../{subdir}"
        lib_path = f"../{subdir}/support-lib"
        step(f"rm -rf {lib_path} || true")
        step(f"git clone https://github.com/rems-project/lean-sail.git {lib_path}")
        print("Building the support library")
        step("lake build +Sail:c.o", cwd=lib_path)
        return f"../../support-lib"

def test_lean(subdir: str, skip_list = None, runnable: bool = False):
    """
    Run all Sail files available in the `subdir`.
    If `runnable` is set to `True`, it will do `lake run`
    instead of `lake build`.
    """
    banner("Cloning the support library")
    support_lib = get_support_lib(subdir)
    print("...done!")
    banner(f'Testing lean target (sub-directory: {subdir})')
    results = Results(subdir)
    for filenames in chunks(os.listdir(f'../{subdir}'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            is_skip = False

            if skip_list is not None and basename in skip_list:
                if run_skips:
                    is_skip = True
                else:
                    print_skip(filename)
                    continue

            tests[filename] = os.fork()
            if tests[filename] == 0:
                os.chdir(f'../{subdir}')
                step('rm -rf {} || true'.format(basename))
                step('mkdir -p {}'.format(basename))
                # TODO: should probably be dependent on whether print should be pure or effectful.
                extra_flags = [
                    '--splice',
                    'rocq-print.splice',
                    '--strict-bitvector',
                ] if runnable else [ ]
                if not runnable:
                    extra_flags.append('--lean-matchbv')
                extra_flags = ' '.join(extra_flags)
                step("'{}' {} {} --lean --lean-single-file  --lean-executable --lean-output-dir {} --lean-lib-path {}".format(
                    sail, extra_flags, filename, basename, support_lib), name=filename)
                step('lake update', cwd=f'{basename}/out', name=filename)
                expected_status = 0
                if runnable and basename.startswith('fail'):
                    expected_status = 1
                if runnable:
                    step(f'lake exe run > expected 2> err_status',
                        cwd=f'{basename}/out',
                        name=filename,
                        expected_status=expected_status,
                        stderr_file=f'{basename}/out/err_status')
                else:
                    # NOTE: lake --dir does not behave the same as cd $dir && lake build...
                    step('lake update', cwd=f'{basename}/out', name=filename)
                    step('lake build', cwd=f'{basename}/out', name=filename)

                if not runnable:
                    output = f"{basename}/output"
                    step(f'cat {basename}/out/Out/Defs.lean > {output}')
                    step(f'echo >> {output}; echo "XXXXXXXXX" >> {output}; echo >> {output}')
                    step(f'cat {basename}/out/Out.lean >> {output}')
                    status = step_with_status(f'diff {output} {basename}.expected.lean', name=filename)
                    if status != 0:
                        if update_expected:
                            print(f'Overriding file {basename}.expected.lean')
                            step(f'cp {output} {basename}.expected.lean')
                        else:
                            sys.exit(1)
                else:
                    status = step_with_status(f'diff {basename}/out/expected {basename}.expect', name=filename)
                    if status != 0:
                        sys.exit(1)

                step('rm -rf {}'.format(basename))

                if is_skip:
                    print(f'{basename} now passes!')
                print_ok(filename)
                sys.exit(0)
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_lean('lean')
xml += test_lean('c', skip_list=skip_selftests, runnable=True)

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
