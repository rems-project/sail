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

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_patterns(name):
    banner('Testing pattern completeness checker')
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -just_check {} 2> {}.error'.format(sail, filename, basename))
                if filename.startswith('warn'):
                    step('diff {}.error {}.expect'.format(basename, basename))
                else:
                    step('diff {}.error no_error'.format(basename))
                step('rm {}.error'.format(basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_patterns('completeness')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
