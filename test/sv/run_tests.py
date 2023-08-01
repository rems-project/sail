#!/usr/bin/env python3

import os
import re
import sys
import hashlib

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()

skip_tests = {
    'eq_struct',
    'foreach_none',
    'list_mut',
    'flow_restrict',
    'tuple_fun',
    'issue202_1',
    'outcome_impl',
    'all_even_vector_length',
    'tuple_conversion',
    'return_register_ref',
    'warl',
    'assign_rename_bug',
    'list_cons_cons',
    'match_bind',
    'string_take',
    'list_rec_functions2',
    'fast_signed',
    'large_bitvector',
    'cheri128_hsb',
    'poly_pair',
    'issue37',
    'reg_ref',
    'reg_init_let',
    'string_of_bits',
    'either',
    'gvector',
    'fail_assert_mono_bug',
    'zero_length_bv',
    'vector_example',
    'real',
    'downcast_fn',
    'pointer_assign',
    'empty_list',
    'two_mapping',
    'poly_mapping2',
    'option_nest',
    'for_shadow',
    'mapping',
    'list_let',
    'list_scope',
    'vector_subrange_pattern',
    'list_scope3',
    'warl_undef',
    'bitvector',
    'loop_exception',
    'cheri_capreg',
    'special_annot',
    'poly_int_record',
    'list_scope2',
    'single_arg',
    'list_torture',
    'read_write_ram',
    'int64_vector_literal',
    'poly_tup',
    'list_test',
    'struct_mapping',
    'list_rec_functions1',
    'poly_mapping',
    'gvectorlit',
    'xlen_val',
    'extend_simple',
    'issue243_fixed',
    'issue136',
    'zeros_mapping',
    'nested_mapping',
    'reg_32_64',
    'split',
    'tl_pat',
    'poly_simple',
    'real_prop',
    'fail_exception',
    'fail_issue203',
    'new_bitfields',
    'implicits',
    'encdec',
}

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_sv(name, skip_list):
    banner('Testing {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir('../c'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            if basename in skip_list:
                print_skip(filename)
                continue
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -no_warn -sv ../c/{} -o {} -sv_verilate run > {}.out'.format(sail, filename, basename, basename))
                step('awk \'/TEST START/{{flag=1;next}}/TEST END/{{flag=0}}flag\' {}.out > {}.result'.format(basename, basename))
                step('diff ../c/{}.expect {}.result'.format(basename, basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_sv('SystemVerilog', skip_tests)

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
