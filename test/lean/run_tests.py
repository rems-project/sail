#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

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
}

class LeanTests(SailTest):
    def run(self):
        banner("Cloning the support library")
        support_lib_lean = self._get_support_lib('lean')
        print("...done!")
        banner('Testing lean target (sub-directory: lean)')
        self.run_tests('lean', os.listdir('../lean'),
                       self._make_test('lean', support_lib_lean, runnable=False))

        banner("Cloning the support library")
        support_lib_c = self._get_support_lib('c')
        print("...done!")
        banner('Testing lean target (sub-directory: c)')
        self.run_tests('c (lean runnable)', os.listdir('../c'),
                       self._make_test('c', support_lib_c, runnable=True, skip_list=skip_selftests),
                       skip_fn=self._make_skip_fn(skip_selftests))

    def _get_support_lib(self, subdir):
        local = args.lean_local_support_library
        if local:
            return local
        lib_path = '../{}/support-lib'.format(subdir)
        step('rm -rf {} || true'.format(lib_path))
        step('git clone https://github.com/rems-project/lean-sail.git {}'.format(lib_path))
        print("Building the support library")
        step('lake build', cwd=lib_path)
        return '../../support-lib'

    def _make_skip_fn(self, skip_list):
        def skip_fn(filename, basename):
            return not args.run_skips and basename in skip_list
        return skip_fn

    def _make_test(self, subdir, support_lib, runnable, skip_list=None):
        def fn(filename, basename):
            is_skip = skip_list is not None and basename in skip_list and args.run_skips
            os.chdir('../{}'.format(subdir))
            step('rm -rf {} || true'.format(basename))
            step('mkdir -p {}'.format(basename))
            extra_flags = (
                ['--splice', 'coq-print.splice', '--strict-bitvector'] if runnable
                else ['--lean-matchbv']
            )
            extra_flags_str = ' '.join(extra_flags)
            step("'{}' {} {} --lean --lean-single-file --lean-executable --lean-output-dir {} --lean-lib-path {}".format(
                self.sail, extra_flags_str, filename, basename, support_lib), name=filename)
            step('lake update', cwd='{}/out'.format(basename), name=filename)
            if runnable:
                expected_status = 1 if basename.startswith('fail') else 0
                step('lake exe run > expected 2> err_status',
                     cwd='{}/out'.format(basename), name=filename,
                     expected_status=expected_status,
                     stderr_file='{}/out/err_status'.format(basename))
            else:
                step('lake update', cwd='{}/out'.format(basename), name=filename)
                step('lake build', cwd='{}/out'.format(basename), name=filename)

            if not runnable:
                output = '{}/output'.format(basename)
                step('cat {}/out/Out/Defs.lean > {}'.format(basename, output))
                step('echo >> {0}; echo "XXXXXXXXX" >> {0}; echo >> {0}'.format(output))
                step('cat {}/out/Out.lean >> {}'.format(basename, output))
                status = step_with_status('diff {} {}.expected.lean'.format(output, basename), name=filename)
                if status != 0:
                    if args.update_expected:
                        print('Overriding file {}.expected.lean'.format(basename))
                        step('cp {} {}.expected.lean'.format(output, basename))
                    else:
                        sys.exit(1)
            else:
                status = step_with_status('diff {}/out/expected {}.expect'.format(basename, basename), name=filename)
                if status != 0:
                    sys.exit(1)

            step('rm -rf {}'.format(basename))
            if is_skip:
                print('{} now passes!'.format(basename))
        return fn

LeanTests().main()
