import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "coq")
_TYPECHECK_PASS_DIR = os.path.join(_SUITE_DIR, "..", "typecheck", "pass")
_COQ_PASS_DIR = os.path.join(_SUITE_DIR, "pass")

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


@suite("coq")
class CoqTests(SailTest):
    def run(self):
        for lib in ["stdpp", "bbv"] if self._have_bbv() else ["stdpp"]:
            xfails = (
                {**_common_xfails, **_bbv_xfails} if lib == "bbv" else _common_xfails
            )
            self.banner(f"Testing Coq backend on typecheck tests with {lib}")
            self.run_tests(
                f"typecheck tests on {lib}",
                Batcher(_TYPECHECK_PASS_DIR),
                self._make_test(_TYPECHECK_PASS_DIR, lib),
                testdir=_SUITE_DIR,
                expected_failures=xfails,
                skip_set=skip_tests,
            )
            self.banner(f"Testing Coq backend on Coq specific tests with {lib}")
            self.run_tests(
                f"Coq specific tests on {lib}",
                Batcher(_COQ_PASS_DIR),
                self._make_test(_COQ_PASS_DIR, lib),
                testdir=_SUITE_DIR,
                expected_failures=xfails,
                skip_set=skip_tests,
            )

    def _have_bbv(self):
        try:
            p = subprocess.run(["coqtop", "-require", "bbv.Word", "-batch"])
            if p.returncode == 0:
                return True
            print("bbv not found, skipping bbv tests")
            return False
        except Exception as e:
            print("Unable to check for bbv")
            print(e)
            return False

    def _make_test(self, src_dir, lib):
        def fn(test):
            step(f"mkdir -p _build_{test.basename}")
            step(
                f"'{self.sail}' --coq --coq-lib-style {lib} --dcoq-undef-axioms"
                f" --strict-bitvector --coq-output-dir _build_{test.basename}"
                f" -o out {src_dir}/{test.filename}"
            )
            os.chdir(f"_build_{test.basename}")
            step("coqc out_types.v", name=test.basename)
            step("coqc out.v", name=test.basename)
            os.chdir("..")
            step(f"rm -r _build_{test.basename}")

        return fn
