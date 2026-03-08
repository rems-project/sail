#!/usr/bin/env python3

import os
import re
import sys
import shutil

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.join(mydir, ".."))

from sailtest import *

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


class SmtTests(SailTest):
    def run(self):
        if shutil.which("cvc4") is not None:
            banner("Testing SMT: cvc4")
            self.run_tests(
                "cvc4",
                os.listdir("."),
                self._make_test("cvc4", "cvc4 --lang=smt2.6", ""),
                skip_fn=self._make_skip_fn("cvc4"),
            )
        else:
            print(
                "{}Cannot find SMT solver cvc4 skipping tests{}".format(
                    color.WARNING, color.END
                )
            )

        if shutil.which("z3") is not None:
            banner("Testing SMT: z3")
            self.run_tests(
                "z3",
                os.listdir("."),
                self._make_test("z3", "z3", ""),
                skip_fn=self._make_skip_fn("z3"),
            )
        else:
            print(
                "{}Cannot find SMT solver z3 skipping tests{}".format(
                    color.WARNING, color.END
                )
            )

    def _make_skip_fn(self, solver_name):
        def skip_fn(filename, basename):
            replaced = basename.replace(".", "_")
            return replaced in _skip_tests and solver_name in _skip_tests[replaced]

        return skip_fn

    def _make_test(self, name, solver, sail_opts):
        def fn(filename, basename):
            basename = basename.replace(".", "_")
            step(
                "'{}' {} -smt {} -o {}".format(self.sail, sail_opts, filename, basename)
            )
            step(
                "timeout 30s {} {}_prop.smt2 1> {}.out".format(
                    solver, basename, basename
                )
            )
            if re.match(r".+\.sat\.sail$", filename):
                step("grep -q ^sat$ {}.out".format(basename))
            else:
                step("grep -q ^unsat$ {}.out".format(basename))

        return fn


SmtTests().main()
