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
targets = get_targets(['ocaml', 'ocaml_trace'])

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))
print("Targets: {}".format(targets))

def test_ocaml(name, opts):
    banner(f'{name} with options: "{opts}"')
    results = Results(name)
    for dirs in directory_chunks(os.listdir('.'), parallel()):
        tests = {}
        for dir in dirs:
            tests[dir] = os.fork()
            if tests[dir] == 0:
                step(f'{sail} --strict-bitvector --no-warn -o out --ocaml {opts} ../prelude.sail *.sail', cwd=dir)
                step('./out > result 2> /dev/null', cwd=dir)
                step('diff expect result', cwd=dir)
                step('rm out', cwd=dir)
                step('rm result', cwd=dir)
                step('rm -rf _sbuild', cwd=dir)
                print_ok(dir)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

if 'ocaml' in targets:
    xml += test_ocaml('Ocaml testing', '')

if 'ocaml_trace' in targets:
    xml += test_ocaml('Ocaml trace testing', '--ocaml-trace')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
