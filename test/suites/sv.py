import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "sv")
_EXEC_DIR = os.path.join(_SUITE_DIR, "..", "exec")

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


class _SvTests(SailTest):
    def prepare(self):
        exec_includes = os.path.join(_EXEC_DIR, "includes")
        work_exec_includes = os.path.join(self.work_dir, "includes")
        if os.path.exists(exec_includes) and not os.path.exists(work_exec_includes):
            shutil.copytree(exec_includes, work_exec_includes)
        sv_include = os.path.join(_SUITE_DIR, "include")
        work_sv_include = os.path.join(self.work_dir, "include")
        if os.path.exists(sv_include) and not os.path.exists(work_sv_include):
            shutil.copytree(sv_include, work_sv_include)

    def run_with_opts(self, name, opts, just_check):
        self.banner(f"Testing {name} with options:{opts}")
        self.run_tests(
            name,
            Batcher(_EXEC_DIR),
            self._make_test(opts, just_check=just_check),
            skip_set=skip_tests,
        )

    def _make_test(self, opts, just_check):
        def fn(test):
            test.copy_filename()
            if test.basename.startswith("fail") or just_check:
                step(
                    f"'{self.sail}' --no-warn --sv {test.filename} -o {test.basename}"
                    f" --sv-verilate compile{opts} --sv-verilate-jobs 1 > {test.basename}.out"
                )
            else:
                step(
                    f"'{self.sail}' --no-warn --sv {test.filename} -o {test.basename}"
                    f" --sv-verilate run{opts} --sv-verilate-jobs 1 > {test.basename}.out"
                )
                step(
                    f"awk '/SAIL START/{{flag=1;next}}/SAIL END/{{flag=0}}flag'"
                    f" {test.basename}.out > {test.basename}.result"
                )
                step(f"diff {test.expect} {test.basename}.result")

        return fn

@suite("sv.default")
class SvDefaultTests(_SvTests):
    def run(self):
        self.run_with_opts("SystemVerilog", "", False)

@suite("sv.nostrings")
class SvNoStringsTests(_SvTests):
    def run(self):
        self.run_with_opts("SystemVerilog (no-strings)", " --sv-no-strings", True)
