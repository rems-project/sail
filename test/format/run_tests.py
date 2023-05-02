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

def test(test_dir):
    banner('Testing {}'.format(test_dir))
    results = Results(test_dir)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('cp {} {}/{}'.format(filename, test_dir, filename))
                step('{} -config {}/config.json -fmt {}/{}'.format(sail, test_dir, test_dir, filename))
                step('diff {}/{} {}/{}.expect'.format(test_dir, filename, test_dir, basename))
                step('rm {}/{}'.format(test_dir, filename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()


xml = '<testsuites>\n'

xml += test('default')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
