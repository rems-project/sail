import os
import sys
import shutil


from sailtest import *

_TEST_DIR = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
)
_SUITE_DIR = os.path.join(_TEST_DIR, "smt")

# Maps replaced basename (dots→underscores) to the set of solvers to skip for
_skip_tests = {
    "assembly_mapping_sat": {"z3", "cvc4"},  # This test using unsupported CVC4 features
    "arith_unsat": {"z3", "cvc4"},
    "arith_LFL_unsat": {"z3", "cvc4"},
    "store_load_sat": {"z3", "cvc4"},
    "load_store_dep_sat": {"z3", "cvc4"},
    "store_load_scattered_sat": {"z3", "cvc4"},
    "mem_builtins_unsat": {"z3", "cvc4"},
    "arith_FFL_3_unsat": {"cvc4"},
    "arith_LCBL_unsat": {"cvc4"},
    "arith_LC32L_3_unsat": {"cvc4"},
    "arith_FFL_5_unsat": {"cvc4"},
}


@suite("smt", _SUITE_DIR)
class SmtTests(SailTest):
    def run(self):
        if shutil.which("cvc4") is not None:
            self.banner("Testing SMT: cvc4")
            self.run_tests(
                "cvc4",
                Batcher(_SUITE_DIR),
                self._make_test("cvc4", "cvc4 --lang=smt2.6", ""),
                testdir=_SUITE_DIR,
                skip_fn=self._make_skip_fn("cvc4"),
            )
        else:
            print(
                f"{color.WARNING}Cannot find SMT solver cvc4 skipping tests{color.END}"
            )

        if shutil.which("z3") is not None:
            self.banner("Testing SMT: z3")
            self.run_tests(
                "z3",
                Batcher(_SUITE_DIR),
                self._make_test("z3", "z3", ""),
                testdir=_SUITE_DIR,
                skip_fn=self._make_skip_fn("z3"),
            )
        else:
            print(f"{color.WARNING}Cannot find SMT solver z3 skipping tests{color.END}")

    def _make_skip_fn(self, solver_name):
        def skip_fn(filename, basename):
            replaced = basename.replace(".", "_")
            return replaced in _skip_tests and solver_name in _skip_tests[replaced]

        return skip_fn

    def _make_test(self, name, solver, sail_opts):
        def fn(filename, basename):
            basename = basename.replace(".", "_")
            step(f"'{self.sail}' {sail_opts} -smt {filename} -o {basename}")
            step(f"timeout 30s {solver} {basename}_prop.smt2 1> {basename}.out")
            if filename.endswith(".sat.sail"):
                step(f"grep -q ^sat$ {basename}.out")
            else:
                step(f"grep -q ^unsat$ {basename}.out")

        return fn
