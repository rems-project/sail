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

def test_lean():
    banner('Testing lean target')
    results = Results('lean')
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('rm -r {} || true'.format(basename))
                step('mkdir -p {}'.format(basename))
                step('\'{}\' {} --lean --lean-output-dir {}'.format(sail, filename, basename))
                # NOTE: lake --dir does not behave the same as cd $dir && lake build...
                step('lake build', cwd=f'{basename}/out')
                step('diff {}/out/Out.lean {}.expected.lean'.format(basename, basename))
                step('rm -r {}'.format(basename))
                print_ok(filename)
                sys.exit(0)
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_lean()

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
