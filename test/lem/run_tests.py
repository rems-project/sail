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
    'vector_pattern_split'
}

print('Sail is {}'.format(sail))
print('Sail dir is {}'.format(sail_dir))

def test_lem():
    banner('Testing lem')
    results = Results('pass')
    for filenames in chunks(os.listdir(test_dir), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            if basename in skip_tests:
                continue
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -lem -o {} {}/{}'.format(sail, basename, test_dir, filename))
                step('lem -lib {}/src/gen_lib {}_types.lem {}.lem'.format(sail_dir, basename, basename))
                step('rm {}_types.lem {}.lem'.format(basename, basename))
                print_ok(filename)
                sys.exit(0)
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_lem()

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
