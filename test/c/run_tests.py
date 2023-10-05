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

def no_valgrind():
    try:
        subprocess.call(['valgrind', '--version'])
        return False
    except FileNotFoundError:
        return True

def test_c(name, c_opts, sail_opts, valgrind, compiler='cc'):
    banner('Testing {} with C options: {} Sail options: {} valgrind: {}'.format(name, c_opts, sail_opts, valgrind))
    results = Results(name)
    if compiler == 'c++':
        # tl_pat.c:66:31: error: ‘zX::<unnamed union>::<unnamed struct>::zX’ has the same name as the class in which it is declared
        results.expect_failure("tl_pat.sail", "same name as the class in which it is declared")
    if valgrind and no_valgrind():
        print('skipping because no valgrind found')
        return results.finish()
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -no_warn -c {} {} 1> {}.c'.format(sail, sail_opts, filename, basename))
                step('{} {} {}.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}.bin'.format(compiler, c_opts, basename, sail_dir, sail_dir, basename))
                step('./{}.bin > {}.result 2> {}.err_result'.format(basename, basename, basename), expected_status = 1 if basename.startswith('fail') else 0)
                step('diff {}.result {}.expect'.format(basename, basename))
                if os.path.exists('{}.err_expect'.format(basename)):
                    step('diff {}.err_result {}.err_expect'.format(basename, basename))
                if valgrind and not basename.startswith('fail'):
                    step("valgrind --leak-check=full --track-origins=yes --errors-for-leak-kinds=all --error-exitcode=2 ./{}.bin".format(basename), expected_status = 1 if basename.startswith('fail') else 0)
                step('rm {}.c {}.bin {}.result'.format(basename, basename, basename))
                print_ok(filename)
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
                step('{} -no_warn -c2 {} {} -o {}'.format(sail, sail_opts, filename, basename))
                step('gcc {} {}.c {}_emu.c {}/lib/*.c -lgmp -lz -I {}/lib -o {}'.format(c_opts, basename, basename, sail_dir, sail_dir, basename))
                step('./{} > {}.result 2>&1'.format(basename, basename), expected_status = 1 if basename.startswith('fail') else 0)
                step('diff {}.result {}.expect'.format(basename, basename))
                if valgrind:
                    step("valgrind --leak-check=full --track-origins=yes --errors-for-leak-kinds=all --error-exitcode=2 ./{}".format(basename), expected_status = 1 if basename.startswith('fail') else 0)
                step('rm {}.c {} {}.result'.format(basename, basename, basename))
                print_ok(filename)
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
                step('{} -undefined_gen -is execute.isail -iout {}.iresult {}'.format(sail, basename, filename))
                step('diff {}.iresult {}.expect'.format(basename, basename))
                step('rm {}.iresult'.format(basename))
                print_ok(filename)
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
                step('{} -ocaml -ocaml_build_dir _sbuild_{} -o {}_ocaml {}'.format(sail, basename, basename, filename))
                step('./{}_ocaml 1> {}.oresult'.format(basename, basename), expected_status = 1 if basename.startswith('fail') else 0)
                step('diff {}.oresult {}.expect'.format(basename, basename))
                step('rm -r _sbuild_{}'.format(basename))
                step('rm {}.oresult {}_ocaml'.format(basename, basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_lem(name):
    banner('Testing {}'.format(name))
    results = Results(name)
    results.expect_failure("inc_tests.sail", "missing built-in functions for increasing vectors in Lem library")
    results.expect_failure("read_write_ram.sail", "uses memory primitives not provided by default in Lem")
    results.expect_failure("for_shadow.sail", "Pure loops aren't current supported for Lem (and don't really make sense)")
    results.expect_failure("fail_exception.sail", "try-blocks around pure expressions not supported in Lem (and a little silly)")
    results.expect_failure("loop_exception.sail", "try-blocks around pure expressions not supported in Lem (and a little silly)")
    results.expect_failure("real.sail", "print_real not available for Lem at present")
    results.expect_failure("real_prop.sail", "print_real not available for Lem at present")
    results.expect_failure("concurrency_interface.sail", "test doesn't meet Lem library's expectations for the concurrency interface")
    results.expect_failure("pc_no_wildcard.sail", "register type unsupported by Lem backend")
    results.expect_failure("cheri_capreg.sail", "test has strange 'pure' reg_deref")
    results.expect_failure("constructor247.sail", "don't attempt to support so many constructors in lem -> ocaml builds")
    results.expect_failure("either.sail", "Lem breaks because it has the same name as a library module")
    results.expect_failure("poly_outcome.sail", "test doesn't meet Lem library's expectations for the concurrency interface")
    results.expect_failure("poly_mapping.sail", "test requires non-standard hex built-ins")
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('{} -lem -lem_lib Undefined_override -o {} {}'.format(sail, basename, filename))
                step('mkdir -p _lbuild_{}'.format(basename))
                step('cp {}/*.lem _lbuild_{}'.format(basename, basename))
                step('cp lbuild/* _lbuild_{}'.format(basename))
                step('cp {}/src/gen_lib/*.lem _lbuild_{}'.format(sail_dir, basename))
                os.chdir('_lbuild_{}'.format(basename))
                step('../mk_lem_ocaml_main.sh {} {}'.format(basename, basename.capitalize()))
                step('ocamlbuild -use-ocamlfind main.native'.format(basename, basename))
                step('./main.native 1> {}.lresult 2> {}.lerr'.format(basename, basename), expected_status = 1 if basename.startswith('fail') else 0)
                step('diff ../{}.expect {}.lresult'.format(basename, basename))
                if os.path.exists('../{}.err_expect'.format(basename)):
                    step('diff {}.lerr ../{}.err_expect'.format(basename, basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

def test_coq(name):
    banner('Testing {}'.format(name))
    results = Results(name)
    results.expect_failure("inc_tests.sail", "missing built-in functions for increasing vectors in Coq library")
    results.expect_failure("read_write_ram.sail", "uses memory primitives not provided by default in Coq")
    results.expect_failure("for_shadow.sail", "Pure loops aren't current supported for Coq (and don't really make sense)")
    results.expect_failure("fail_exception.sail", "try-blocks around pure expressions not supported in Coq (and a little silly)")
    results.expect_failure("loop_exception.sail", "try-blocks around pure expressions not supported in Coq (and a little silly)")
    results.expect_failure("concurrency_interface.sail", "test doesn't meet Coq library's expectations for the concurrency interface")
    results.expect_failure("outcome_impl.sail", "test doesn't meet Coq backend's expectations for the concurrency interface")
    results.expect_failure("pc_no_wildcard.sail", "register type unsupported by Coq backend")
    results.expect_failure("cheri_capreg.sail", "test has strange 'pure' reg_deref")
    results.expect_failure("poly_outcome.sail", "test doesn't meet Coq library's expectations for the concurrency interface")
    results.expect_failure("poly_mapping.sail", "test requires non-standard hex built-ins")
    results.expect_failure("real_prop.sail", "random_real not available for Coq at present")
    results.expect_failure("fail_assert_mono_bug.sail", "test output checking not supported for Coq yet")
    results.expect_failure("fail_issue203.sail", "test output checking not supported for Coq yet")
    results.expect_failure("vector_example.sail", "bug: function defs and function calls treat 'len equation differently in Coq backedn")
    results.expect_failure("list_torture.sail", "Coq backend doesn't remove a phantom type parameter")
    results.expect_failure("tl_pat.sail", "Coq backend doesn't support constructors with the same name as a type")
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                # Generate Coq from Sail
                step('{} -coq -undefined_gen -o {} {}'.format(sail, basename, filename))

                step('mkdir -p _coqbuild_{}'.format(basename))
                step('mv {}.v _coqbuild_{}'.format(basename, basename))
                step('mv {}_types.v _coqbuild_{}'.format(basename, basename))
                step('./mk_coq_main.sh {} {}'.format(basename, basename.capitalize()))
                os.chdir('_coqbuild_{}'.format(basename))

                # TODO: find bbv properly
                step('coqc {}_types.v'.format(basename))
                step('coqc {}.v'.format(basename))
                step('coqtop -require-import {}_types -require-import {} -l main.v -batch | tee /dev/stderr | grep -q OK'.format(basename,basename))

                os.chdir('..')
                step('rm -r _coqbuild_{}'.format(basename))

                print('{} {}{}{}'.format(filename, color.PASS, 'ok', color.END))
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

#xml += test_c2('unoptimized C', '', '', True)
xml += test_c('unoptimized C', '', '', False)
xml += test_c('unoptimized C with C++ compiler', '-xc++', '', False, compiler='c++')
xml += test_c('optimized C', '-O2', '-O', True)
xml += test_c('optimized C with C++ compiler', '-xc++ -O2', '-O', True, compiler='c++')
xml += test_c('constant folding', '', '-Oconstant_fold', False)
#xml += test_c('monomorphised C', '-O2', '-O -Oconstant_fold -auto_mono', True)
xml += test_c('undefined behavior sanitised', '-O2 -fsanitize=undefined', '-O', False)

xml += test_interpreter('interpreter')

xml += test_ocaml('OCaml')

#xml += test_lem('lem')
#xml += test_coq('coq')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
