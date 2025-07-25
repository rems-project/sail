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

skip_tests = {
  'while_PM', # Not currently in a useful state
  'type_pow_zero', # uses cvc4, not worth rerunning for rocq output
}

def test(name, dir, lib):
    banner('Testing Coq backend on {} with {}'.format(name, lib))
    results = Results('{} on {}'.format(name, lib))
    results.expect_failure('exist1.sail', 'Needs an existential witness')
    results.expect_failure('while_MM.sail', 'Non-terminating loops - I\'ve written terminating versions of these')
    results.expect_failure('while_MP.sail', 'Non-terminating loops - I\'ve written terminating versions of these')
    results.expect_failure('while_PM.sail', 'Non-terminating loops - I\'ve written terminating versions of these')
    results.expect_failure('while_PP.sail', 'Non-terminating loops - I\'ve written terminating versions of these')
    results.expect_failure('repeat_constraint.sail', 'Non-terminating loop that\'s only really useful for the type checking tests')
    results.expect_failure('while_MM_terminating.sail', 'Not yet - haven\'t decided whether to support register reads in measures')
    results.expect_failure('floor_pow2.sail', 'TODO, add termination measure')
    results.expect_failure('try_while_try.sail', 'TODO, add termination measure')
    results.expect_failure('no_val_recur.sail', 'TODO, add termination measure')
    results.expect_failure('phantom_option.sail', 'Type variables that need to be filled in')
    results.expect_failure('rebind.sail', 'Variable shadowing')
    results.expect_failure('exist_tlb.sail', 'Existential that requires more type information')
    results.expect_failure('type_div.sail', 'Essential use of an equality constraint in the context')
    results.expect_failure('concurrency_interface_dec.sail', 'Need to be built against stdpp version of Sail (for now)')
    results.expect_failure('concurrency_interface_inc.sail', 'Need to be built against stdpp version of Sail (for now)')
    results.expect_failure('float_prelude.sail', 'Would need float types in coq-sail')
    results.expect_failure('config_mismatch.sail', 'Uses non-existant configuration entry')
    results.expect_failure('outcome_impl_int.sail', 'Uses outcome in a way that\'t not yet supported')
    results.expect_failure('outcome_int.sail', 'Uses outcome in a way that\'t not yet supported')
    results.expect_failure('existential_parametric.sail', 'Dependent pairs example that we can\'t do yet')
    if lib == 'bbv':
        results.expect_failure('sysreg.sail', 'Concurrency interface not currently supported on BBV')
        results.expect_failure('type_alias.sail', 'Concurrency interface not currently supported on BBV')

    for filenames in chunks(os.listdir(dir), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            if basename in skip_tests:
                print_skip(filename)
                continue
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('mkdir -p _build_{}'.format(basename))
                step('\'{}\' --coq --coq-lib-style {} --dcoq-undef-axioms --strict-bitvector --coq-output-dir _build_{} -o out {}/{}'.format(sail, lib, basename, dir, filename))
                os.chdir('_build_{}'.format(basename))
                step('coqc out_types.v', name=basename)
                step('coqc out.v', name=basename)
                os.chdir('..')
                step('rm -r _build_{}'.format(basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test('typecheck tests', '../typecheck/pass', 'stdpp')
xml += test('Coq specific tests', 'pass', 'stdpp')

try:
    p = subprocess.run(["coqtop", "-require", "bbv.Word", "-batch"])
    if p.returncode == 0:
        xml += test('typecheck tests', '../typecheck/pass', 'bbv')
        xml += test('Coq specific tests', 'pass', 'bbv')
    else:
        print("bbv not found, skipping bbv tests")
except Exception as e:
    print("Unable to check for bbv")
    print(e)

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()

