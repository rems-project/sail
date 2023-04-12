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

print('Sail is {}'.format(sail))
print('Sail dir is {}'.format(sail_dir))

step('mkdir -p rtpass')
step('mkdir -p rtpass2')

def test_pass():
    banner('Testing passing programs')
    results = Results('pass')
    for filenames in chunks(os.listdir('pass'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -no_memo_z3 -just_check -ddump_tc_ast pass/{} 1> rtpass/{}'.format(sail, filename, filename))
                step('{} -no_memo_z3 -just_check -ddump_tc_ast -dmagic_hash -dno_cast rtpass/{} 1> rtpass2/{}'.format(sail, filename, filename))
                step('diff rtpass/{} rtpass2/{}'.format(filename, filename))
                i = 0
                variantdir = os.path.join('pass', basename);
                for variantname in os.listdir(variantdir) if os.path.isdir(variantdir) else []:
                    if re.match('.+\.sail$', variantname):
                        variantbasename = os.path.splitext(os.path.basename(variantname))[0]
                        step('{} -no_memo_z3 pass/{}/{} 2> pass/{}/{}.error'.format(sail, basename, variantname, basename, variantbasename), expected_status = 1)
                        step('diff pass/{}/{}.error pass/{}/{}.expect'.format(basename, variantbasename, basename, variantbasename))
                        step('rm pass/{}/{}.error'.format(basename, variantbasename))
                        i = i + 1
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_fail():
    banner('Testing failing programs')
    results = Results('fail')
    for filenames in chunks(os.listdir('fail'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -no_memo_z3 fail/{} 2> fail/{}.error'.format(sail, filename, basename), expected_status = 1)
                step('diff fail/{}.error fail/{}.expect'.format(basename, basename))
                step('rm fail/{}.error'.format(basename))
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
