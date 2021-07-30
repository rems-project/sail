#!/usr/bin/env python2

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
                step('gcc {} {}.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}.bin'.format(c_opts, basename, sail_dir, sail_dir, basename))
                step('./{}.bin 1> {}.result'.format(basename, basename), expected_status = 1 if basename == "exception" else 0)
                step('diff {}.result {}.expect'.format(basename, basename))
                if valgrind:
                    step("valgrind --leak-check=full --track-origins=yes --errors-for-leak-kinds=all --error-exitcode=2 ./{}.bin".format(basename), expected_status = 1 if basename == "exception" else 0)
                step('rm {}.c {}.bin {}.result'.format(basename, basename, basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_c2(name, c_opts, sail_opts, valgrind):
    banner('Testing {} with C (-c2) options: {} Sail options: {} valgrind: {}'.format(name, c_opts, sail_opts, valgrind))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('sail -no_warn -c2 {} {} -o {}'.format(sail_opts, filename, basename))
                step('gcc {} {}.c {}_emu.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}'.format(c_opts, basename, basename, sail_dir, sail_dir, basename))
                step('./{} 1> {}.result'.format(basename, basename), expected_status = 1 if basename == "exception" else 0)
                step('diff {}.result {}.expect'.format(basename, basename))
                if valgrind:
                    step("valgrind --leak-check=full --track-origins=yes --errors-for-leak-kinds=all --error-exitcode=2 ./{}".format(basename), expected_status = 1 if basename == "exception" else 0)
                step('rm {}.c {} {}.result'.format(basename, basename, basename))
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
                step('sail -undefined_gen -is execute.isail -iout {}.iresult {}'.format(basename, filename))
                step('diff {}.iresult {}.expect'.format(basename, basename))
                step('rm {}.iresult'.format(basename))
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
                step('sail -ocaml -ocaml_build_dir _sbuild_{} -o {}_ocaml {}'.format(basename, basename, filename))
                step('./{}_ocaml 1> {}.oresult'.format(basename, basename), expected_status = 1 if basename == "exception" else 0)
                step('diff {}.oresult {}.expect'.format(basename, basename))
                step('rm -r _sbuild_{}'.format(basename))
                step('rm {}.oresult {}_ocaml'.format(basename, basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_lem(name):
    banner('Testing {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('sail -lem {}'.format(filename))
                step('mkdir -p _lbuild_{}'.format(basename))
                step('cp {}*.lem _lbuild_{}'.format(basename, basename))
                step('cp lbuild/* _lbuild_{}'.format(basename))
                step('cp ../../src/gen_lib/*.lem _lbuild_{}'.format(basename))
                os.chdir('_lbuild_{}'.format(basename))
                step('echo "let _ = {}.main ()" > main.ml'.format(basename.capitalize()))
                step('ocamlbuild -use-ocamlfind main.native'.format(basename, basename))
                step('./main.native 1> {}.lresult'.format(basename))
                step('diff ../{}.expect {}.lresult'.format(basename, basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

#xml += test_c2('unoptimized C', '', '', True)
xml += test_c('unoptimized C', '', '', True)
xml += test_c('optimized C', '-O2', '-O', True)
xml += test_c('constant folding', '', '-Oconstant_fold', True)
xml += test_c('monomorphised C', '-O2', '-O -Oconstant_fold -auto_mono', True)
xml += test_c('undefined behavior sanitised', '-O2 -fsanitize=undefined', '-O', False)

xml += test_interpreter('interpreter')

xml += test_ocaml('OCaml')

#xml += test_lem('lem')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
