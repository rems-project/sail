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
    'all_even_vector_length',
    'assign_rename_bug',
    'bitvector', # This requires -sv_bits_size >= 200
    'cheri128_hsb',
    'cheri_capreg', # replicate bits
    'empty_list',
    'eq_struct',
    'fail_assert_mono_bug',
    'fail_issue203', # dec_str
    'for_shadow',
    'foreach_none',
    'gvector',
    'gvectorlit', # generic vectors
    'int64_vector_literal',
    'issue136', # lists
    'issue202_1', # lists
    'large_bitvector', # This requires -sv_bits_size >= 204
    'list_cons_cons',
    'list_let',
    'list_mut',
    'list_rec_functions1', # lists
    'list_rec_functions2',
    'list_scope',
    'list_scope2',
    'list_scope3',
    'list_test', # lists
    'list_torture',
    'loop_exception',
    'pointer_assign',
    'poly_mapping', # length
    'poly_mapping2',
    'read_write_ram',
    'real',
    'real_prop', # reals
    'reg_32_64', # register references
    'split', # generic vectors
    'string_of_bits',
    'string_take',
    'tl_pat', # identifier and type identifier
    'tuple_conversion', # verilator fails?
    'vector_example',
    'vector_subrange_pattern',
    'warl',
    'warl_undef',
    'xlen_val', # Calls external C function
    'zero_length_bv',
}

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_sv(name, opts, skip_list):
    banner('Testing {} with options:{}'.format(name, opts))
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
                step('{} -no_warn -sv ../c/{} -o {} -sv_verilate run{} > {}.out'.format(sail, filename, basename, opts, basename))
                step('awk \'/TEST START/{{flag=1;next}}/TEST END/{{flag=0}}flag\' {}.out > {}.result'.format(basename, basename))
                step('diff ../c/{}.expect {}.result'.format(basename, basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_sv('SystemVerilog', '', skip_tests)

skip_tests.remove('bitvector')

xml += test_sv('SystemVerilog', ' -sv_int_size 128 -sv_bits_size 256', skip_tests)

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
