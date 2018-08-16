#!/usr/bin/env python

import os
import re
import sys
import hashlib

sail_dir = os.environ['SAIL_DIR']
os.chdir(os.path.dirname(__file__))
sys.path.insert(0, os.path.join(sail_dir, 'test'))

from sailtest import *

def test_c(name, c_opts, sail_opts, valgrind):
    banner('Testing {} with C options: {} Sail options: {} valgrind: {}'.format(name, c_opts, sail_opts, valgrind))
    tests = {}
    for filename in os.listdir('.'):
        if re.match('.+\.sail', filename):
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('sail -no_warn -c {} {} 1> {}.c'.format(sail_opts, filename, basename))
                step('gcc {} {}.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}'.format(c_opts, basename, sail_dir, sail_dir, basename))
                step('./{} 1> {}.result'.format(basename, basename))
                step('diff {}.result {}.expect'.format(basename, basename))
                if valgrind:
                    step("valgrind --leak-check=full --errors-for-leak-kinds=all --error-exitcode=1 ./{}".format(basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
    return collect_results(name, tests)

xml = '<testsuites>\n'

xml += test_c('unoptimized C', '', '', True)
xml += test_c('optimized C', '-O2', '-O', True)
xml += test_c('address sanitised', '-O2 -fsanitize=undefined', '-O', False)

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
