#!/usr/bin/env python

import os
import re
import sys
import hashlib

sail_dir = os.environ['SAIL_DIR']
os.chdir(os.path.dirname(__file__))
sys.path.insert(0, os.path.join(sail_dir, 'test'))

from sailtest import *

def test_c_builtins(name, sail_opts):
    banner('Testing builtins: {} Sail options: {}'.format(name, sail_opts))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('sail -no_warn -c {} {} 1> {}.c'.format(sail_opts, filename, basename))
                step('gcc {}.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}'.format(basename, sail_dir, sail_dir, basename))
                step('./{}'.format(basename))
                step('rm {}.c'.format(basename))
                step('rm {}'.format(basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
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
                step('sail -no_warn -ocaml -ocaml_build_dir _sbuild_{} -o {} {}'.format(basename, basename, filename))
                step('./{}'.format(basename))
                step('rm -r _sbuild_{}'.format(basename))
                step('rm {}'.format(basename))
                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
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
                step('sail -no_warn -lem {}'.format(filename))

                # Create a directory to build the generated Lem and
                # copy/move everything we need into it, as well as
                # making a symlink to gen_lib for ocamlbuild
                step('mkdir -p _lbuild_{}'.format(basename))
                step('mv {}.lem _lbuild_{}'.format(basename, basename))
                step('mv {}_types.lem _lbuild_{}'.format(basename, basename))
                step('cp myocamlbuild.ml _lbuild_{}'.format(basename))
                os.chdir('_lbuild_{}'.format(basename))
                step('ln -s $SAIL_DIR/src/gen_lib/ gen_lib')

                # Use ocamlbuild to build the lem to OCaml using the
                # myocamlbuild.ml rule
                step('ocamlbuild -I gen_lib -package lem {}.native'.format(basename))
                step('./{}.native'.format(basename))

                # Cleanup the build directory
                os.chdir('..')
                step('rm -r _lbuild_{}'.format(basename))

                print '{} {}{}{}'.format(filename, color.PASS, 'ok', color.END)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_c_builtins('C, No optimisations', '')
xml += test_c_builtins('C, Optimisations', '-O')
xml += test_c_builtins('C, Constant folding', '-Oconstant_fold')

xml += test_ocaml_builtins('OCaml', '')

# Comment this out for most runs because it's really slow
# xml += test_lem_builtins('Lem to OCaml')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()

