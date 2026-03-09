import os
import sys
import shutil


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "smt")

# Maps replaced test.basename (dots→underscores) to the set of solvers to skip for
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


class _SmtTests(SailTest):
    def run_with_solver(self, solver, command):
        if shutil.which(solver) is not None:
            self.banner(f"Testing SMT: {solver}")
            self.run_tests(
                solver,
                Batcher(_SUITE_DIR),
                self._make_test(solver, command, ""),
                skip_fn=self._make_skip_fn(solver),
            )
        else:
            print(
                f"{Color.WARNING}Cannot find SMT solver {solver} skipping tests{Color.END}"
            )

    def _make_skip_fn(self, solver_name):
        def skip_fn(test):
            replaced = test.basename.replace(".", "_")
            return replaced in _skip_tests and solver_name in _skip_tests[replaced]

        return skip_fn

    def _make_test(self, name, solver, sail_opts):
        def fn(test):
            test.copy_filename()
            basename = test.basename.replace(".", "_")
            step(f"'{self.sail}' {sail_opts} -smt {test.filename} -o {basename}")
            step(f"timeout 30s {solver} {basename}_prop.smt2 1> {basename}.out")
            if test.filename.endswith(".sat.sail"):
                step(f"grep -q ^sat$ {basename}.out")
            else:
                step(f"grep -q ^unsat$ {basename}.out")

        return fn


@suite("smt.z3")
class Z3Tests(_SmtTests):
    def run(self):
        self.run_with_solver("z3", "z3")


@suite("smt.cvc4")
class Cvc4Tests(_SmtTests):
    def run(self):
        self.run_with_solver("cvc4", "cvc4 --lang=smt2.6")
