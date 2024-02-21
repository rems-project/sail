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

sailcov = '{}/sailcov/sailcov'.format(sail_dir)

def have_sailcov():
    try:
        subprocess.call([sailcov, '--help'], stdout=subprocess.DEVNULL)
        return True
    except FileNotFoundError:
        return False

def test_sailcov():
    banner('Testing sailcov')
    results = Results('sailcov')
    if not have_sailcov():
        print('Skipping because no sailcov executable found')
        return results.finish()
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -no_warn -no_memo_z3 -c -c_include sail_coverage.h -c_coverage {}.branches -c_coverage_output {}.taken {} -o {}'.format(sail, basename, basename, filename, basename))
                step('cc {}.c {}/lib/*.c {}/lib/coverage/libsail_coverage.a -lgmp -lz -lpthread -ldl -I {}/lib -o {}.bin'.format(basename, sail_dir, sail_dir, sail_dir, basename))
                step('./{}.bin'.format(basename))
                step('{} --all {}.branches --taken {}.taken {}'.format(sailcov, basename, basename, filename))
                step('diff {}.html {}.expect'.format(basename, basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_sailcov()

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
