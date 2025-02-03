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
}

def test(name, dir):
    banner('Testing Coq backend on {}'.format(name))
    results = Results(name)
    results.expect_failure('bind_typ_var.sail', 'unsupported existential quantification of a vector length')
    results.expect_failure('execute_decode_hard.sail', 'Complex existential type - probably going to need this for ARM instruction ASTs')
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
    results.expect_failure('existential_constraint_synonym.sail', 'not yet supported existential type (probably quite easy?)')
    results.expect_failure('eqn_inst.sail', 'Type variables that need to be filled in')
    results.expect_failure('phantom_option.sail', 'Type variables that need to be filled in')
    results.expect_failure('plus_one_unify.sail', 'Type variables that need to be filled in')
    results.expect_failure('rebind.sail', 'Variable shadowing')
    results.expect_failure('exist_tlb.sail', 'Existential that should produce a pair')
    results.expect_failure('ast_with_dep_tuple.sail', 'A use of an existential type that\'s not supported yet')
    results.expect_failure('equation_arguments.sail', 'Essential use of an equality constraint in the context')
    results.expect_failure('multiple_unifiers.sail', 'Essential use of an equality constraint in the context')
    results.expect_failure('type_div.sail', 'Essential use of an equality constraint in the context')
    results.expect_failure('concurrency_interface_dec.sail', 'Need to be built against stdpp version of Sail (for now)')
    results.expect_failure('concurrency_interface_inc.sail', 'Need to be built against stdpp version of Sail (for now)')
    results.expect_failure('ex_cons_infer.sail', 'Would need to turn a term with existential type into a dependent pair')
    results.expect_failure('ex_list_infer.sail', 'Would need to turn a term with existential type into a dependent pair')
    results.expect_failure('ex_vector_infer.sail', 'Would need to turn a term with existential type into a dependent pair')
    results.expect_failure('float_prelude.sail', 'Would need float types in coq-sail')
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
                step('\'{}\' --coq --coq-lib-style stdpp --dcoq-undef-axioms --strict-bitvector --coq-output-dir _build_{} -o out {}/{}'.format(sail, basename, dir, filename))
                os.chdir('_build_{}'.format(basename))
                step('coqc out_types.v')
                step('coqc out.v')
                os.chdir('..')
                step('rm -r _build_{}'.format(basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test('typecheck tests', '../typecheck/pass')
xml += test('Coq specific tests', 'pass')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()

