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

sail_dir = get_sail_dir()
sail = get_sail()

# Self-tests refers to self contained Sail programs in test/c/ which are Sail programs
# that you can run to exercise the language and the extracted output.
# Not all self-tests are supported.
skip_selftests = {
    'list_rec_functions2',
    'eq_struct',
    'either_rvbug',
    'bv_literal',
    'issue362',
    'prelude',
    'pow2_var',
    'large_bitvector',
    'exn_hello_world',
    'poly_union_rev',
    'match_bind',
    'rev_bits_in_byte',
    'foreach_none',
    'all_even_vector_length',
    'outcome_impl',
    'lib_valid_hex_bits',
    'tuple_conversion',
    'pow2',
    'primop',
    'zero_length_bv',
    'poly_pair',
    'issue37',
    'assign_rename_bug',
    'warl',
    'config',
    'spc_mappings_small',
    'cheri128_hsb',
    'instruction',
    'gvector',
    'small_slice',
    'union_variant_names',
    'lib_hex_bits',
    'lib_hex_bits_signed',
    'fail_assert_mono_bug',
    'config_bit',
    'varswap',
    'rv_format2',
    'try_return',
    'bitvector_update2',
    'real',
    'inc_tests',
    'poly_outcome',
    'string_of_bits',
    'nexp_synonym',
    'return_leak',
    'custom_flow',
    'pointer_assign',
    'two_mapping',
    'ctz',
    'spc_mappings',
    'concurrency_interface',
    'vector_example',
    'reg_init_let',
    'for_shadow',
    'list_torture',
    'rv_format',
    'option_nest',
    'string_literal_type',
    'hex_str_negative',
    'xlen32',
    'issue232_2',
    'cheri_capreg',
    'loop_exception',
    'issue429',
    'pc_no_wildcard',
    'type_if_bits',
    'poly_union',
    'dec_str_fixed',
    'bitvector_update',
    'nested_fields',
    'nexp_simp_euclidian',
    'config_register_ones',
    'toplevel_tyvar',
    'ediv',
    'ediv_from_tdiv',
    'int_struct',
    'int64_vector_literal',
    'concurrency_interface_write',
    'read_write_ram',
    'enum_vector',
    'issue136',
    'reg_32_64',
    'issue232',
    'issue243_fixed',
    'int_struct_constrained',
    'get_slice_int',
    'fail_exception',
    'zeros_mapping',
    'natural_sort_reg',
    'option_option',
    'anf_as_pattern',
    'implicits',
    'simple_bitmanip',
    'poly_mapping',
    'gvectorlit',
    'fvector_update',
    'split',
    'new_bitfields',
    'real_prop',
    'vector_init',
    'partial_mapping',
    'fail_issue203',
    'lib_dec_bits'
}

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_lean(subdir: str, skip_list = None, runnable: bool = False):
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
                step('rm -r {} || true'.format(basename))
                step('mkdir -p {}'.format(basename))
                # TODO: should probably be dependent on whether print should be pure or effectful.
                extra_flags = ' '.join([
                    '--splice',
                    'coq-print.splice'
                ] if runnable else [ ])
                step('\'{}\' {} {} --lean --lean-output-dir {}'.format(sail, extra_flags, filename, basename), name=filename)
                if runnable:
                    step(f'lake exe run > expected 2> err_status', cwd=f'{basename}/out', name=filename)
                else:
                    # NOTE: lake --dir does not behave the same as cd $dir && lake build...
                    step('lake build', cwd=f'{basename}/out', name=filename)

                if not runnable:
                    status = step_with_status(f'diff {basename}/out/Out.lean {basename}.expected.lean', name=filename)
                    if status != 0:
                        if update_expected:
                            print(f'Overriding file {basename}.expected.lean')
                            step(f'cp {basename}/out/Out.lean {basename}.expected.lean')
                        else:
                            sys.exit(1)
                else:
                    status = step_with_status(f'diff {basename}/out/expected {basename}.expect', name=filename)
                    if status != 0:
                        sys.exit(1)

                step('rm -r {}'.format(basename))

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
