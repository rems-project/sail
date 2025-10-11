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

def chunks(filenames, cores):
    ys = []
    chunk = []
    for filename in filenames:
        chunk.append(filename)
        if len(chunk) >= cores:
            ys.append(list(chunk))
            chunk = []
    ys.append(list(chunk))
    return ys

libraries=['values', 'operators', 'instr_kinds', 'prompt_monad', 'prompt', 'operators_mwords', 'state_monad', 'state', 'string', 'undefined']
joiner = ' '
libpaths = joiner.join(['{}/src/gen_lib/sail2_{}.lem'.format(sail_dir, lib) for lib in libraries])
libml = joiner.join(['sail2_{}.ml'.format(lib) for lib in libraries])

def test():
    banner('Monomorphisation tests')
    results = Results('mono')
    for filenames in chunks(os.listdir('pass'), parallel()):
        tests = {}
        for filename in filenames:
            tests[filename] = os.fork()
            if tests[filename] == 0:
                with open('pass/{}'.format(filename)) as f:
                    arguments = f.read()
                step('mkdir -p _build_{}'.format(filename))
                step('\'{}\' --lem --lem-mwords --lem-lib Test_extra --lem-output-dir _build_{} -o out {}'.format(sail, filename, arguments))
                os.chdir('_build_{}'.format(filename))
                step('lem -ocaml -lib {}/src/lem_interp {} -outdir . ../test_extra.lem out_types.lem out.lem'.format(sail_dir, libpaths))
                step('if grep -q initial_regstate out.lem; then cp ../test_with_state.ml test.ml; else cp ../test.ml test.ml; fi')
                step('ocamlfind ocamlc -linkpkg -package zarith -package lem {} test_extra.ml out_types.ml out.ml test.ml'.format(libml))
                os.chdir('..')
                step('rm -r _build_{}'.format(filename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'
xml += test()
xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
