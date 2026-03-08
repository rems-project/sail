#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

skip_tests = {
    'all_even_vector_length', # loops
    'for_shadow', # loops
    'loop_exception', # loops
    'loop_termination', # loops
    'read_write_ram', # memory
    'real', # reals
    'real_prop', # reals
    'split', # loops
    'vector_example', # loops
    'nexp_simp_euclidian', # division
    'concurrency_interface', # memory
    'ediv_from_tdiv', # loops
    'lib_hex_bits_signed', # verilator bug (in CI, works with latest)
    'hex_bits_backwards', # verilator bug (in CI, works with latest)
    'lib_dec_bits', # todo
    'config_vec_list', # unknown length vectors
    'simple_while', # loops
    'simple_while2', # loops
    'simple_while3', # loops
    'concurrency_interface_v2',
    'concurrency_interface_v2_var',
    'mini_builtins', # unsupported builtins
}

class SvTests(SailTest):
    def run(self):
        banner('Testing SystemVerilog with options:')
        self.run_tests('SystemVerilog', os.listdir('../c'),
                       self._make_test('', just_check=False),
                       skip_set=skip_tests)

        banner('Testing SystemVerilog (nostrings) with options: --sv-no-strings')
        self.run_tests('SystemVerilog (nostrings)', os.listdir('../c'),
                       self._make_test(' --sv-no-strings', just_check=True),
                       skip_set=skip_tests)

    def _make_test(self, opts, just_check):
        def fn(filename, basename):
            step('rm -rf {}_obj_dir'.format(basename))
            if basename.startswith('fail') or just_check:
                step('\'{}\' --no-warn --sv ../c/{} -o {} --sv-verilate compile{} --sv-verilate-jobs 1 > {}.out'.format(
                    self.sail, filename, basename, opts, basename))
            else:
                step('\'{}\' --no-warn --sv ../c/{} -o {} --sv-verilate run{} --sv-verilate-jobs 1 > {}.out'.format(
                    self.sail, filename, basename, opts, basename))
                step('awk \'/SAIL START/{{flag=1;next}}/SAIL END/{{flag=0}}flag\' {}.out > {}.result'.format(
                    basename, basename))
                step('diff ../c/{}.expect {}.result'.format(basename, basename))
        return fn

SvTests().main()
