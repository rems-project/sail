#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *

skip_tests = {
    "all_even_vector_length",  # loops
    "for_shadow",  # loops
    "loop_exception",  # loops
    "loop_termination",  # loops
    "read_write_ram",  # memory
    "real",  # reals
    "real_prop",  # reals
    "split",  # loops
    "vector_example",  # loops
    "nexp_simp_euclidian",  # division
    "concurrency_interface",  # memory
    "ediv_from_tdiv",  # loops
    "lib_hex_bits_signed",  # verilator bug (in CI, works with latest)
    "hex_bits_backwards",  # verilator bug (in CI, works with latest)
    "lib_dec_bits",  # todo
    "config_vec_list",  # unknown length vectors
    "simple_while",  # loops
    "simple_while2",  # loops
    "simple_while3",  # loops
    "concurrency_interface_v2",
    "concurrency_interface_v2_var",
    "mini_builtins",  # unsupported builtins
}


class SvTests(SailTest):
    def run(self):
        opts = ""
        self.banner(f"Testing SystemVerilog with options: {opts}")
        self.run_tests(
            "SystemVerilog",
            os.listdir("../c"),
            self._make_test(opts, just_check=False),
            skip_set=skip_tests,
        )

        opts = "--sv-no-strings"
        self.banner(f"Testing SystemVerilog (nostrings) with options: {opts}")
        self.run_tests(
            "SystemVerilog (nostrings)",
            os.listdir("../c"),
            self._make_test(f" {opts}", just_check=True),
            skip_set=skip_tests,
        )

    def _make_test(self, opts, just_check):
        def fn(filename, basename):
            step(f"rm -rf {basename}_obj_dir")
            if basename.startswith("fail") or just_check:
                step(
                    f"'{self.sail}' --no-warn --sv ../exec/{filename} -o {basename}"
                    f" --sv-verilate compile{opts} --sv-verilate-jobs 1 > {basename}.out"
                )
            else:
                step(
                    f"'{self.sail}' --no-warn --sv ../exec/{filename} -o {basename}"
                    f" --sv-verilate run{opts} --sv-verilate-jobs 1 > {basename}.out"
                )
                step(
                    f"awk '/SAIL START/{{flag=1;next}}/SAIL END/{{flag=0}}flag'"
                    f" {basename}.out > {basename}.result"
                )
                step(f"diff ../exec/{basename}.expect {basename}.result")

        return fn


SvTests().main()
