#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_float(name, sail_opts, compiler, c_opts):
    banner('Testing {} with C options: {} Sail options: {}'.format(name, c_opts, sail_opts))
    results = Results(name)

    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}

        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]

            if basename == "tuple_equality":
              continue

            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -no_warn -c {} {} 1> {}.c'.format(sail, sail_opts, filename, basename))
                step('{} {} {}.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}.bin'.format(compiler, c_opts, basename, sail_dir, sail_dir, basename))
                step('./{}.bin > {}.result 2> {}.err_result'.format(basename, basename, basename), expected_status = 1 if basename.startswith('fail') else 0)

                step('diff {}.err_result no_error && rm {}.err_result'.format(basename, basename))
                step('rm {}.c {}.bin {}.result'.format(basename, basename, basename))

                print_ok(filename)
                sys.exit()

        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_float('floating point c optimized', '', 'cc', '-O2')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
