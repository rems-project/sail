#!/usr/bin/env python3

import os
import re
import sys
import hashlib

from shutil import which

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()

print('Sail is {}'.format(sail))
print('Sail dir is {}'.format(sail_dir))

def test_fail():
    banner('Testing failing programs for naming conventions')
    results = Results('fail')
    for filenames in chunks(os.listdir('fail'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -o /dev/null -naming_check -naming_check_strict fail/{} 2> fail/{}.error'.format(sail, filename, basename), expected_status = 1)
                step('diff fail/{}.error fail/{}.expect'.format(basename, basename))
                step('rm fail/{}.error'.format(basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_pass():
    banner('Testing passing programs for naming conventions')
    results = Results('pass')
    for filenames in chunks(os.listdir('pass'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step("'{}' -o /dev/null -naming_check pass/{}".format(sail, filename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'
xml += test_pass()
xml += test_fail()
xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
