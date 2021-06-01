#!/usr/bin/env python2

import os
import re
import sys
import hashlib
import distutils.spawn

sail_dir = os.environ['SAIL_DIR']
os.chdir(os.path.dirname(__file__))
sys.path.insert(0, os.path.join(sail_dir, 'test'))

from sailtest import *

def test_smt(name, solver, sail_opts):
    banner('Testing SMT: {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            basename = basename.replace('.', '_')
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('sail {} -smt {} -o {}'.format(sail_opts, filename, basename))
                step('timeout 300s {} {}_prop.smt2 1> {}.out'.format(solver, basename, basename))
                if re.match('.+\.sat\.sail$', filename):
                    step('grep -q ^sat$ {}.out'.format(basename))
                else:
                    step('grep -q ^unsat$ {}.out'.format(basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
        results.collect(tests)
    return results.finish()
    return collect_results(name, tests)

xml = '<testsuites>\n'

if distutils.spawn.find_executable('cvc4'):
    xml += test_smt('cvc4', 'cvc4 --lang=smt2.6', '')
else:
    print '{}Cannot find SMT solver cvc4 skipping tests{}'.format(color.WARNING, color.END)

#if distutils.spawn.find_executable('z3'):
#    xml += test_smt('z3', 'z3', '')
#else:
#    print '{}Cannot find SMT solver cvc4 skipping tests{}'.format(color.WARNING, color.END)

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()

