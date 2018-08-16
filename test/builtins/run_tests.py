#!/usr/bin/env python

import os
import re
import sys
import hashlib

sail_dir = os.environ['SAIL_DIR']
os.chdir(os.path.dirname(__file__))
sys.path.insert(0, os.path.join(sail_dir, 'test'))

from sailtest import *

def test_builtins(name, sail_opts):
    banner('Testing builtins: {} Sail options: {}'.format(name, sail_opts))
    tests = {}
    for filename in os.listdir('.'):
        if re.match('.+\.sail', filename):
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('sail -no_warn -c {} {} 1> {}.c'.format(sail_opts, filename, basename))
                step('gcc {}.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}'.format(basename, sail_dir, sail_dir, basename))
                step('./{}'.format(basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
    return collect_results(name, tests)

xml = '<testsuites>\n'

test_builtins('No optimisations', '')
test_builtins('Optimisations', '-O')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
