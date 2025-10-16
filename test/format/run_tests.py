#!/usr/bin/env python3

import os
import re
import sys
import hashlib

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

update_expected = args.update_expected

sail_dir = get_sail_dir()
sail = get_sail()

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test(test_dir):
    banner(f'Testing {test_dir}')
    results = Results(test_dir)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step(f'cp {filename} {test_dir}/{filename}')
                step(f'\'{sail}\' --sail-config {test_dir}/config.json --fmt {test_dir}/{filename}')
                status = step_with_status(f'diff {test_dir}/{filename} {test_dir}/{basename}.expect')
                if status != 0:
                    if update_expected:
                        print(f'Overriding file {test_dir}/{basename}.expected')
                        step(f'\'{sail}\' --sail-config {test_dir}/config.json --fmt {filename} --fmt-emit stdout > {test_dir}/{basename}.expect')
                    else:
                        sys.exit(1)
                step(f'rm {test_dir}/{filename}')
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()


xml = '<testsuites>\n'

xml += test('default')
xml += test('lw80_preserve')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
