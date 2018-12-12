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
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('sail -no_warn -c {} {} 1> {}.c'.format(sail_opts, filename, basename))
                step('gcc {} {}.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}'.format(c_opts, basename, sail_dir, sail_dir, basename))
                step('./{} 1> {}.result'.format(basename, basename))
                step('diff {}.result {}.expect'.format(basename, basename))
                if valgrind:
                    step("valgrind --leak-check=full --track-origins=yes --errors-for-leak-kinds=all --error-exitcode=1 ./{}".format(basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_interpreter(name):
    banner('Testing {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('sail -is execute.isail -iout {}.iresult {}'.format(basename, filename))
                step('diff {}.iresult {}.expect'.format(basename, basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_ocaml(name):
    banner('Testing {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('sail -ocaml -ocaml_build_dir _sbuild_{} -o {} {}'.format(basename, basename, filename))
                step('./{} 1> {}.oresult'.format(basename, basename))
                step('diff {}.oresult {}.expect'.format(basename, basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_c('unoptimized C', '', '', True)
xml += test_c('optimized C', '-O2', '-O', True)
xml += test_c('constant folding', '', '-Oconstant_fold', True)
xml += test_c('full optimizations', '-O2 -mbmi2 -DINTRINSICS', '-O -Oconstant_fold', True)
xml += test_c('address sanitised', '-O2 -fsanitize=undefined', '-O', False)

xml += test_interpreter('interpreter')

xml += test_ocaml('OCaml')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
