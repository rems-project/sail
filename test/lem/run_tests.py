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

test_dir = '../typecheck/pass'

skip_tests = {
    'phantom_option',
    'phantom_bitlist_union',
    # The Lem backend needs sail_mem_read to be instantiated at a minimum
    'concurrency_interface_dec',
    'concurrency_interface_inc',
}
skip_tests_mwords = {
    'phantom_option',
    'overload_plus',
    'vector_append_gen',
    'execute_decode_hard',
    'simple_record_access',
    'vector_append',
    'existential_constraint_synonym',
    'exist_tlb',
    'negative_bits_union',
    'while_MM',
    'while_PM',
    'zero_length_bv',
    'negative_bits_list',
    'patternrefinement',
    # Due to an incompatibility between -auto_mono and -smt_linearize
    'pow_32_64',
    # The Lem backend needs sail_mem_read to be instantiated at a minimum
    'concurrency_interface_dec',
    'concurrency_interface_inc',
}

print('Sail is {}'.format(sail))
print('Sail dir is {}'.format(sail_dir))

def test_lem(name, opts, skip_list):
    banner('Testing Lem {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir(test_dir), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            if basename in skip_list:
                print_skip(filename)
                continue
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -lem {} -o {} {}/{}'.format(sail, opts, basename, test_dir, filename))
                step('lem -lib {}/src/gen_lib {}_types.lem {}.lem'.format(sail_dir, basename, basename))
                step('rm {}_types.lem {}.lem'.format(basename, basename))
                print_ok(filename)
                sys.exit(0)
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_lem('with bitlists', '', skip_tests)
xml += test_lem('with machine words', '-lem_mwords -auto_mono', skip_tests_mwords)

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
