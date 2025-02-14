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
# TODO: once we support many of those, we should make this a `skip_selftests`
skip_selftests = {
    'struct_pattern_partial',
    'issue202_1',
    'list_rec_functions2',
    'eq_struct',
    'either_rvbug',
    'bv_literal',
    'issue362',
    'return_register_ref',
    'prelude',
    'tuple_fun',
    'pow2_var',
    'large_bitvector',
    'exn_hello_world',
    'struct',
    'poly_union_rev',
    'match_bind',
    'sv_dpi',
    'rev_bits_in_byte',
    'foreach_none',
    'letbind',
    'enum_map',
    'all_even_vector_length',
    'outcome_impl',
    'lib_valid_hex_bits',
    'string_of_bits2',
    'list_cons_cons',
    'tuple_conversion',
    'pow2',
    'primop',
    'reg_ref',
    'zero_length_bv',
    'reg_ref_nb',
    'poly_pair',
    'fast_signed',
    'issue37',
    'assign_rename_bug',
    'warl',
    'config',
    'if_opt_typ',
    'spc_mappings_small',
    'cheri128_hsb',
    'instruction',
    'overload_mapping',
    'encdec_subrange',
    'gvector',
    'small_slice',
    'union_variant_names',
    'lib_hex_bits',
    'lib_hex_bits_signed',
    'fail_assert_mono_bug',
    'constructor247',
    'config_bit',
    'varswap',
    'struct_fn_arg',
    'rv_format2',
    'let_option_shadow',
    'try_return',
    'bitvector_update2',
    'poly_mapping2',
    'real',
    'inc_tests',
    'poly_outcome',
    'string_of_bits',
    'nexp_synonym',
    'config_register',
    'return_leak',
    'custom_flow',
    'pointer_assign',
    'either',
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
    'vector_subrange_pattern',
    'string_literal_type',
    'hex_str_negative',
    'single_arg',
    'shadow_let',
    'tuple_union',
    'bitvector',
    'xlen32',
    'rv_duopod_bug',
    'mapping',
    'issue232_2',
    'poly_int_record',
    'cheri_capreg',
    'loop_exception',
    'issue429',
    'list_list_eq',
    'list_test',
    'struct_mapping',
    'pc_no_wildcard',
    'type_if_bits',
    'poly_union',
    'dec_str_fixed',
    'unused_poly_ctor',
    'bitvector_update',
    'nested_fields',
    'nexp_simp_euclidian',
    'tl_let',
    'config_register_ones',
    'toplevel_tyvar',
    'pattern_concat_nest',
    'option',
    'abstract_type',
    'poly_tup',
    'ediv',
    'ediv_from_tdiv',
    'int_struct',
    'dead_branch',
    'int64_vector_literal',
    'concurrency_interface_write',
    'read_write_ram',
    'enum_vector',
    'list_rec_functions1',
    'issue136',
    'reg_32_64',
    'issue232',
    'issue243_fixed',
    'enum_functions',
    'int_struct_constrained',
    'get_slice_int',
    'fail_exception',
    'zeros_mapping',
    'extend_simple',
    'natural_sort_reg',
    'option_option',
    'pr194',
    'tl_pat',
    'anf_as_pattern',
    'implicits',
    'simple_bitmanip',
    'poly_mapping',
    'xlen_val',
    'nested_mapping',
    'gvectorlit',
    'encdec',
    'infix_include',
    'fvector_update',
    'split',
    'struct_pattern',
    'stack_struct',
    'new_bitfields',
    'real_prop',
    'vector_init',
    'partial_mapping',
    'fail_issue203'
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
