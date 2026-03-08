#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

_cpp_xfails = {
    'cabbrev.sail': 'my_pair_in_c is declared in a namespace in C++',
    'xlen_val.sail': 'assumes variables are still global',
    # TODO: These use `$c_in_main` to add a call to `sail_set_abstract_xlen(32)` to `main()`
    # but for C++ it needs to go in `model_main()` and be `model.sail_set_abstract_xlen(32)`.
    'abstract_sizeof_no_use.sail': 'difficult to call model.sail_set_abstract_... in the right place',
    'abstract_type.sail': 'difficult to call model.sail_set_abstract_... in the right place',
    'tl_let_flow_change.sail': 'difficult to call model.sail_set_abstract_... in the right place',
}

def _no_valgrind():
    try:
        subprocess.call(['valgrind', '--version'])
        return False
    except FileNotFoundError:
        return True

class CTests(SailTest):
    def run(self):
        targets = get_targets(['c', 'cpp', 'interpreter', 'ocaml'])
        print("Targets: {}".format(targets))

        if 'c' in targets:
            banner('Testing unoptimized C with C options:  Sail options: --c-no-mangle valgrind: False')
            self._run_c_tests('unoptimized C', '', '--c-no-mangle', False)

            banner('Testing unoptimized C with C options:  Sail options:  valgrind: False')
            self._run_c_tests('unoptimized C', '', '', False)

            banner('Testing optimized C with C options: -O2 Sail options: -O valgrind: True')
            self._run_c_tests('optimized C', '-O2', '-O', True)

            banner('Testing constant folding with C options:  Sail options: -Oconstant_fold valgrind: False')
            self._run_c_tests('constant folding', '', '-Oconstant_fold', False)

            banner('Testing undefined behavior sanitised with C options: -O2 -fsanitize=undefined Sail options: -O valgrind: False')
            self._run_c_tests('undefined behavior sanitised', '-O2 -fsanitize=undefined', '-O', False)

            banner('Testing address sanitised with C options: -O2 -fsanitize=address -g Sail options: -O valgrind: False')
            self._run_c_tests('address sanitised', '-O2 -fsanitize=address -g', '-O', False)

        if 'cpp' in targets:
            # Compiling the C as if it was C++.
            banner('Testing unoptimized C with C++ compiler with C options: -xc++ Sail options:  valgrind: False')
            self._run_c_tests('unoptimized C with C++ compiler', '-xc++', '', False, compiler='c++')

            banner('Testing optimized C with C++ compiler with C options: -xc++ -O2 Sail options: -O valgrind: True')
            self._run_c_tests('optimized C with C++ compiler', '-xc++ -O2', '-O', True, compiler='c++')

            # Actual C++ output.
            banner('Testing unoptimized C++ with C options:  Sail options:  valgrind: False')
            self._run_c_tests('unoptimized C++', '', '', False, compiler='c++', actually_cpp=True,
                               expected_failures=_cpp_xfails)

            banner('Testing optimized C++ with C options: -O2 Sail options: -O valgrind: True')
            self._run_c_tests('optimized C++', '-O2', '-O', True, compiler='c++', actually_cpp=True,
                               expected_failures=_cpp_xfails)

        if 'interpreter' in targets:
            if os.name == 'posix':
                banner('Testing interpreter')
                self.run_tests('interpreter', os.listdir('.'), self._test_interpreter)
            else:
                print('Skipping interpreter tests because the interpreter is only supported on Unix-like platforms')

        if 'ocaml' in targets:
            banner('Testing OCaml')
            self.run_tests('OCaml', os.listdir('.'), self._test_ocaml)

        if 'lem' in targets:
            banner('Testing lem')
            self.run_tests('lem', os.listdir('.'), self._test_lem,
                           expected_failures={
                               'inc_tests.sail': 'missing built-in functions for increasing vectors in Lem library',
                               'read_write_ram.sail': 'uses memory primitives not provided by default in Lem',
                               'fail_exception.sail': 'try-blocks around pure expressions not supported in Lem (and a little silly)',
                               'loop_exception.sail': 'try-blocks around pure expressions not supported in Lem (and a little silly)',
                               'real.sail': 'print_real not available for Lem at present',
                               'real_prop.sail': 'print_real not available for Lem at present',
                               'concurrency_interface.sail': 'test doesn\'t meet Lem library\'s expectations for the concurrency interface',
                               'concurrency_interface_v2.sail': 'test doesn\'t meet Lem library\'s expectations for the concurrency interface',
                               'concurrency_interface_write.sail': 'test harness doesn\'t meet Lem library\'s expectations for the concurrency interface',
                               'pc_no_wildcard.sail': 'register type unsupported by Lem backend',
                               'cheri_capreg.sail': 'test has strange \'pure\' reg_deref',
                               'constructor247.sail': 'don\'t attempt to support so many constructors in lem -> ocaml builds',
                               'either.sail': 'Lem breaks because it has the same name as a library module',
                               'poly_outcome.sail': 'test doesn\'t meet Lem library\'s expectations for the concurrency interface',
                               'config_abstract_bool.sail': 'type-level if not yet supported',
                               'outcome_impl_int.sail': 'unsupported outcome',
                               'outcome_impl_bool.sail': 'unsupported outcome',
                           })

        if 'coq' in targets:
            banner('Testing coq')
            self.run_tests('coq', os.listdir('.'), self._test_coq,
                           expected_failures={
                               'inc_tests.sail': 'missing built-in functions for increasing vectors in Coq library',
                               'read_write_ram.sail': 'uses memory primitives not provided by default in Coq',
                               'fail_exception.sail': 'test harness can\'t produce expected output for uncaught exception',
                               'loop_exception.sail': 'Loop requiring termination measure with a register read',
                               'outcome_impl.sail': 'test doesn\'t meet Coq backend\'s expectations for the concurrency interface',
                               'outcome_impl_int.sail': 'test doesn\'t meet Coq backend\'s expectations for the concurrency interface',
                               'outcome_impl_bool.sail': 'test doesn\'t meet Coq backend\'s expectations for the concurrency interface',
                               'pc_no_wildcard.sail': 'register type unsupported by Coq backend',
                               'poly_outcome.sail': 'test doesn\'t meet Coq library\'s expectations for the concurrency interface',
                               'poly_mapping.sail': 'test requires non-standard hex built-ins',
                               'real.sail': 'print_real not available for Coq at present',
                               'real_prop.sail': 'random_real not available for Coq at present',
                               'for_shadow.sail': 'bug: remove_e_assign rewrite assumes <= available',
                               'newtype.sail': 'Type definition with a parameter that should be merged, inferred, or made explicit',
                               'simple_while.sail': 'Loop without termination measure',
                               'simple_while2.sail': 'Loop without termination measure',
                               'simple_while3.sail': 'Loop without termination measure',
                           })

    def _run_c_tests(self, name, c_opts, sail_opts, valgrind, compiler='cc', actually_cpp=False,
                     expected_failures=None):
        """Run a C/C++ test suite, handling the valgrind-unavailable case."""
        if valgrind and _no_valgrind():
            print('skipping because no valgrind found')
            self._xml_parts.append(Results(name).finish())
            return
        extension = 'cpp' if actually_cpp else 'c'
        target_opt = '--cpp' if actually_cpp else '-c'
        def fn(filename, basename):
            step('\'{}\' --no-warn {} {} {} -o {}'.format(self.sail, target_opt, sail_opts, filename, basename))
            step('{} {} {}.{} \'{}\'/lib/*.c -lgmp -I \'{}\'/lib -o {}.bin'.format(
                compiler, c_opts, basename, extension, self.sail_dir, self.sail_dir, basename))
            step('./{}.bin > {}.result 2> {}.err_result'.format(basename, basename, basename),
                 expected_status=1 if basename.startswith('fail') else 0,
                 stderr_file='{}.err_result'.format(basename))
            step('diff {}.result {}.expect'.format(basename, basename))
            if os.path.exists('{}.err_expect'.format(basename)):
                step('diff {}.err_result {}.err_expect'.format(basename, basename))
            if valgrind and not basename.startswith('fail'):
                step('valgrind --leak-check=full --track-origins=yes --errors-for-leak-kinds=all --error-exitcode=2 ./{}.bin'.format(basename),
                     expected_status=1 if basename.startswith('fail') else 0)
            step('rm {}.{} {}.h {}.bin {}.result'.format(basename, extension, basename, basename, basename))
        self.run_tests(name, os.listdir('.'), fn, expected_failures=expected_failures)

    def _test_interpreter(self, filename, basename):
        step('timeout 10s \'{}\' -undefined_gen -is execute.isail -iout {}.iresult {}'.format(
            self.sail, basename, filename))
        step('diff {}.iresult {}.expect'.format(basename, basename))
        step('rm {}.iresult'.format(basename))

    def _test_ocaml(self, filename, basename):
        step(f'\'{self.sail}\' --ocaml --ocaml-build-dir _sbuild_{basename} -o {basename}_ocaml {filename}')
        step(f'dune exec --release {basename}_ocaml 1> ../{basename}.oresult',
             expected_status=1 if basename.startswith('fail') else 0,
             cwd=f'_sbuild_{basename}')
        step(f'diff {basename}.oresult {basename}.expect')
        step(f'rm -rf _sbuild_{basename}')
        step(f'rm {basename}.oresult')

    def _test_lem(self, filename, basename):
        step('\'{}\' -lem -lem_lib Undefined_override -o {} {}'.format(self.sail, basename, filename))
        step('mkdir -p _lbuild_{}'.format(basename))
        step('mv {}.lem {}_types.lem _lbuild_{}'.format(basename, basename, basename))
        step('rm {}_lemmas.thy'.format(basename.capitalize()))
        step('cp lbuild/* _lbuild_{}'.format(basename))
        os.chdir('_lbuild_{}'.format(basename))
        step('../mk_lem_ocaml_main.sh {} {} {}'.format(basename, basename.capitalize(), self.sail_dir))
        step('lem -lib .. -ocaml *.lem')
        step('ocamlbuild -use-ocamlfind main.native'.format(basename, basename))
        step('./main.native 1> {}.lresult 2> {}.lerr'.format(basename, basename),
             expected_status=1 if basename.startswith('fail') else 0)
        step('diff ../{}.expect {}.lresult'.format(basename, basename))
        if os.path.exists('../{}.err_expect'.format(basename)):
            step('diff {}.lerr ../{}.err_expect'.format(basename, basename))
        os.chdir('..')
        step('rm -r _lbuild_{}'.format(basename))

    def _test_coq(self, filename, basename):
        step('\'{}\' -coq -coq-record-update -D PRINT_EFFECTS -splice coq-print.splice -undefined_gen -o {} {}'.format(
            self.sail, basename, filename))
        step('mkdir -p _coqbuild_{}'.format(basename))
        step('mv {}.v _coqbuild_{}'.format(basename, basename))
        step('mv {}_types.v _coqbuild_{}'.format(basename, basename))
        step('./mk_coq_main.sh {} {}'.format(basename, basename.capitalize()))
        os.chdir('_coqbuild_{}'.format(basename))
        step('coqc {}_types.v'.format(basename))
        step('coqc {}.v'.format(basename))
        step('coqtop -require-import {}_types -require-import {} -l main.v -batch | tee /dev/stderr | grep -q OK'.format(
            basename, basename), expected_status=1 if basename.startswith('fail') else 0)
        filter_command = 'ocaml ../coq_output_filter.ml < '
        step('{} output.out | diff - ../{}.expect'.format(filter_command, basename))
        if os.path.exists('../{}.err_expect'.format(basename)):
            step('{} error.out | diff - ../{}.err_expect'.format(filter_command, basename))
        os.chdir('..')
        step('rm -r _coqbuild_{}'.format(basename))

CTests().main()
