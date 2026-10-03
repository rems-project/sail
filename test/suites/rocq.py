import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "rocq")
_TYPECHECK_PASS_DIR = os.path.join(TEST_DIR, "typecheck", "pass")
_ROCQ_PASS_DIR = os.path.join(_SUITE_DIR, "pass")

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

# BBV is not supported at present. If it is re-enabled, these tests are
# expected to fail with it, in addition to the common ones above:
#
#   "sysreg.sail": "Concurrency interface not currently supported on BBV",
#   "type_alias.sail": "Concurrency interface not currently supported on BBV",


@suite("rocq", _SUITE_DIR)
class RocqTests(SailTest):
    def run(self):
        lib = "stdpp"
        self.banner(f"Testing Rocq backend on typecheck tests with {lib}")
        self.run_tests(
            f"typecheck tests on {lib}",
            Batcher(_TYPECHECK_PASS_DIR),
            self._make_test(_TYPECHECK_PASS_DIR, lib),
            testdir=_SUITE_DIR,
            expected_failures=_common_xfails,
            skip_set=skip_tests,
        )
        self.banner(f"Testing Rocq backend on Rocq specific tests with {lib}")
        self.run_tests(
            f"Rocq specific tests on {lib}",
            Batcher(_ROCQ_PASS_DIR),
            self._make_test(_ROCQ_PASS_DIR, lib),
            testdir=_SUITE_DIR,
            expected_failures=_common_xfails,
            skip_set=skip_tests,
        )

    def _make_test(self, src_dir, lib):
        def fn(filename, basename):
            step(f"mkdir -p _build_{basename}")
            step(
                f"'{self.sail}' --rocq --rocq-lib-style {lib} --rocq-undef-axioms"
                f" --strict-bitvector --rocq-output-dir _build_{basename}"
                f" -o out {src_dir}/{filename}"
            )
            os.chdir(f"_build_{basename}")
            step("coqc out_types.v", name=basename)
            step("coqc out.v", name=basename)
            os.chdir("..")
            step(f"rm -r _build_{basename}")

        return fn
