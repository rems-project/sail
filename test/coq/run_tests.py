#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *

skip_tests = {
    "while_PM",  # Not currently in a useful state
    "type_pow_zero",  # uses cvc4, not worth rerunning for rocq output
}

_common_xfails = {
    "exist1.sail": "Needs an existential witness",
    "while_MM.sail": "Non-terminating loops - I've written terminating versions of these",
    "while_MP.sail": "Non-terminating loops - I've written terminating versions of these",
    "while_PM.sail": "Non-terminating loops - I've written terminating versions of these",
    "while_PP.sail": "Non-terminating loops - I've written terminating versions of these",
    "repeat_constraint.sail": "Non-terminating loop that's only really useful for the type checking tests",
    "while_MM_terminating.sail": "Not yet - haven't decided whether to support register reads in measures",
    "floor_pow2.sail": "TODO, add termination measure",
    "try_while_try.sail": "TODO, add termination measure",
    "no_val_recur.sail": "TODO, add termination measure",
    "phantom_option.sail": "Type variables that need to be filled in",
    "rebind.sail": "Variable shadowing",
    "exist_tlb.sail": "Existential that requires more type information",
    "type_div.sail": "Essential use of an equality constraint in the context",
    "concurrency_interface_dec.sail": "Need to be built against stdpp version of Sail (for now)",
    "concurrency_interface_inc.sail": "Need to be built against stdpp version of Sail (for now)",
    "float_prelude.sail": "Would need float types in coq-sail",
    "config_mismatch.sail": "Uses non-existant configuration entry",
    "outcome_impl_int.sail": "Uses outcome in a way that't not yet supported",
    "outcome_int.sail": "Uses outcome in a way that't not yet supported",
    "existential_parametric.sail": "Dependent pairs example that we can't do yet",
}

_bbv_xfails = {
    "sysreg.sail": "Concurrency interface not currently supported on BBV",
    "type_alias.sail": "Concurrency interface not currently supported on BBV",
}


class CoqTests(SailTest):
    def run(self):
        banner("Testing Coq backend on typecheck tests with stdpp")
        self.run_tests(
            "typecheck tests on stdpp",
            os.listdir("../typecheck/pass"),
            self._make_test("../typecheck/pass", "stdpp"),
            expected_failures=_common_xfails,
            skip_set=skip_tests,
        )

        banner("Testing Coq backend on Coq specific tests with stdpp")
        self.run_tests(
            "Coq specific tests on stdpp",
            os.listdir("pass"),
            self._make_test("pass", "stdpp"),
            expected_failures=_common_xfails,
            skip_set=skip_tests,
        )

        try:
            p = subprocess.run(["coqtop", "-require", "bbv.Word", "-batch"])
            if p.returncode == 0:
                bbv_xfails = {**_common_xfails, **_bbv_xfails}
                banner("Testing Coq backend on typecheck tests with bbv")
                self.run_tests(
                    "typecheck tests on bbv",
                    os.listdir("../typecheck/pass"),
                    self._make_test("../typecheck/pass", "bbv"),
                    expected_failures=bbv_xfails,
                    skip_set=skip_tests,
                )

                banner("Testing Coq backend on Coq specific tests with bbv")
                self.run_tests(
                    "Coq specific tests on bbv",
                    os.listdir("pass"),
                    self._make_test("pass", "bbv"),
                    expected_failures=bbv_xfails,
                    skip_set=skip_tests,
                )
            else:
                print("bbv not found, skipping bbv tests")
        except Exception as e:
            print("Unable to check for bbv")
            print(e)

    def _make_test(self, dir, lib):
        def fn(filename, basename):
            step("mkdir -p _build_{}".format(basename))
            step(
                "'{}' --coq --coq-lib-style {} --dcoq-undef-axioms --strict-bitvector --coq-output-dir _build_{} -o out {}/{}".format(
                    self.sail, lib, basename, dir, filename
                )
            )
            os.chdir("_build_{}".format(basename))
            step("coqc out_types.v", name=basename)
            step("coqc out.v", name=basename)
            os.chdir("..")
            step("rm -r _build_{}".format(basename))

        return fn


CoqTests().main()
