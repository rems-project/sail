#!/usr/bin/env python3

import os
import re
import sys
import hashlib
import distutils.spawn


mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.join(mydir, '..'))

from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()

skip_tests = {
    'assembly_mapping_sat': { 'cvc4' }, # This test using unsupported CVC4 features
    'arith_unsat': { 'z3', 'cvc4' },
    'arith_LFL_unsat' : { 'z3', 'cvc4' },
    'revrev_endianness2_unsat' : { 'z3', 'cvc4' }, # There is some bug in this test
}

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_smt(name, solver, sail_opts):
    banner('Testing SMT: {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            basename = basename.replace('.', '_')
            if basename in skip_tests:
                if name in skip_tests[basename]:
                    print_skip(filename)
                    continue
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} {} -smt {} -o {}'.format(sail, sail_opts, filename, basename))
                step('timeout 30s {} {}_prop.smt2 1> {}.out'.format(solver, basename, basename))
                if re.match('.+\.sat\.sail$', filename):
                    step('grep -q ^sat$ {}.out'.format(basename))
                else:
                    step('grep -q ^unsat$ {}.out'.format(basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()
    return collect_results(name, tests)

xml = '<testsuites>\n'

if distutils.spawn.find_executable('cvc4'):
    xml += test_smt('cvc4', 'cvc4 --lang=smt2.6', '')
else:
    print('{}Cannot find SMT solver cvc4 skipping tests{}'.format(color.WARNING, color.END))

if distutils.spawn.find_executable('z3'):
    xml += test_smt('z3', 'z3', '')
else:
    print('{}Cannot find SMT solver z3 skipping tests{}'.format(color.WARNING, color.END))

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()

