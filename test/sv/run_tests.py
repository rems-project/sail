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
    'cheri128_hsb',
    'for_shadow',
    'inc_tests',
    'loop_exception',
    'poly_mapping', # length
    'poly_mapping2',
    'read_write_ram',
    'real', # reals
    'real_prop', # reals
    'split', # generic vectors, loops
    'vector_example', # loops
    'xlen_val', # Calls external C function
    'spc_mappings',
    'lib_hex_bits', # bitvector parsing
    'lib_hex_bits_signed', # bitvector parsing
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
                step('rm -rf {}_obj_dir'.format(basename));
                if basename.startswith('fail'):
                    step('{} -no_warn -sv ../c/{} -o {} -sv_verilate compile{} > {}.out'.format(sail, filename, basename, opts, basename))
                else:
                    step('{} -no_warn -sv ../c/{} -o {} -sv_verilate run{} > {}.out'.format(sail, filename, basename, opts, basename))
                    step('awk \'/SAIL START/{{flag=1;next}}/SAIL END/{{flag=0}}flag\' {}.out > {}.result'.format(basename, basename))
                    step('diff ../c/{}.expect {}.result'.format(basename, basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_sv('SystemVerilog', '', skip_tests)
# xml += test_sv('SystemVerilog', ' -sv_padding', skip_tests) */
# xml += test_sv('SystemVerilog', ' -Oconstant_fold', skip_tests) */
# xml += test_sv('SystemVerilog', ' -sv_specialize 2', skip_tests) */

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
