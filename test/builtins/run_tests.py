#!/usr/bin/env python3

import os
import re
import sys
import hashlib

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.join(mydir, '..'))

from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_c_builtins(name, sail_opts):
    banner('Testing builtins: {} Sail options: {}'.format(name, sail_opts))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -no_warn -c {} {} 1> {}.c'.format(sail, sail_opts, filename, basename))
                step('gcc {}.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}'.format(basename, sail_dir, sail_dir, basename))
                step('./{}'.format(basename))
                step('rm {}.c'.format(basename))
                step('rm {}'.format(basename))
                print('{} {}{}{}'.format(filename, color.PASS, 'ok', color.END))
                sys.exit()
        results.collect(tests)
    return results.finish()
    return collect_results(name, tests)

def test_ocaml_builtins(name, sail_opts):
    banner('Testing builtins: {} Sail options: {}'.format(name, sail_opts))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -no_warn -ocaml -ocaml_build_dir _sbuild_{} -o {} {}'.format(sail, basename, basename, filename))
                step('./{}'.format(basename))
                step('rm -r _sbuild_{}'.format(basename))
                step('rm {}'.format(basename))
                print('{} {}{}{}'.format(filename, color.PASS, 'ok', color.END))
                sys.exit()
        results.collect(tests)
    return results.finish()
    return collect_results(name, tests)

def test_lem_builtins(name):
    banner('Testing builtins: {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                # Generate Lem from Sail
                step('{} -no_warn -lem -o {} {}'.format(sail, basename, filename))

                # Create a directory to build the generated Lem and
                # copy/move everything we need into it, as well as
                # making a symlink to gen_lib for ocamlbuild
                step('mkdir -p _lbuild_{}'.format(basename))
                step('mv {}.lem _lbuild_{}'.format(basename, basename))
                step('mv {}_types.lem _lbuild_{}'.format(basename, basename))
                step('cp myocamlbuild.ml _lbuild_{}'.format(basename))
                step('cp {}/src/gen_lib/*.lem _lbuild_{}'.format(sail_dir, basename))
                os.chdir('_lbuild_{}'.format(basename))

                # Use ocamlbuild to build the lem to OCaml using the
                # myocamlbuild.ml rule
                step('ocamlbuild -package lem {}.native'.format(basename))
                step('./{}.native'.format(basename))

                # Cleanup the build directory
                os.chdir('..')
                step('rm -r _lbuild_{}'.format(basename))

                print('{} {}{}{}'.format(filename, color.PASS, 'ok', color.END))
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_coq_builtins(name):
    banner('Testing builtins: {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                # Generate Coq from Sail
                step('{} -no_warn -coq -undefined_gen -o {} {}'.format(sail, basename, filename))

                step('mkdir -p _coqbuild_{}'.format(basename))
                step('mv {}.v _coqbuild_{}'.format(basename, basename))
                step('mv {}_types.v _coqbuild_{}'.format(basename, basename))
                step('cp test.v _coqbuild_{}'.format(basename))
                os.chdir('_coqbuild_{}'.format(basename))

                # TODO: find bbv properly
                step('coqc {}_types.v'.format(basename))
                step('coqc {}.v'.format(basename))
                step('coqtop -require-import {}_types -require-import {} -l test.v -batch | tee /dev/stderr | grep -q OK'.format(basename,basename))

                os.chdir('..')
                step('rm -r _coqbuild_{}'.format(basename))

                print('{} {}{}{}'.format(filename, color.PASS, 'ok', color.END))
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_isla_builtins(name):
    banner('Testing builtins: {}'.format(name))
    isla_dir = os.environ['ISLA_DIR']
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{}/isla-sail/isla-sail {} {}/lib/vector_dec.sail {}/test/property/include/config.sail -o {}'.format(isla_dir, filename, sail_dir, isla_dir, basename))
                step('{}/target/release/isla-execute-function -A {}.ir -C {}/configs/plain.toml main'.format(isla_dir, basename, isla_dir))
                step('rm {}.ir'.format(basename))
                print('{} {}{}{}'.format(filename, color.PASS, 'ok', color.END))
                sys.exit()
        results.collect(tests)
    return results.finish()
    return collect_results(name, tests)

xml = '<testsuites>\n'

xml += test_c_builtins('C, No optimisations', '')
xml += test_c_builtins('C, Optimisations', '-O')
xml += test_c_builtins('C, Constant folding', '-Oconstant_fold')

xml += test_ocaml_builtins('OCaml', '')

# Comment this out for most runs because it's really slow
# xml += test_lem_builtins('Lem to OCaml')
# xml += test_coq_builtins('Coq')

# Isla is separate, so don't run by default
# For testing symbolic operations in Isla it's useful to tweak the primop macros
# so that the symbolic versions are used even when the values are concrete.
# xml += test_isla_builtins('Isla')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()

