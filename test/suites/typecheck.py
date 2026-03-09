import os
import sys
from shutil import which


from sailtest import *

_TEST_DIR = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
)
_SUITE_DIR = os.path.join(_TEST_DIR, "typecheck")
_PASS_DIR = os.path.join(_SUITE_DIR, "pass")
_PROJECT_DIR = os.path.join(_SUITE_DIR, "project")
_FAIL_DIR = os.path.join(_SUITE_DIR, "fail")


@suite("typecheck.pass", _SUITE_DIR)
class TypecheckPassTests(SailTest):
    def run(self):
        os.makedirs(os.path.join(_SUITE_DIR, "rtpass"), exist_ok=True)
        os.makedirs(os.path.join(_SUITE_DIR, "rtpass2"), exist_ok=True)

        skip_pass = set()
        if which("cvc4") is None:
            skip_pass.add("type_pow_zero")

        self.banner("Testing passing programs")
        self.run_tests(
            "pass",
            Batcher(_PASS_DIR),
            self._test,
            testdir=_SUITE_DIR,
            skip_set=skip_pass,
        )

    def _test(self, filename, basename):
        step(
            f"'{self.sail}' --no-memo-z3 --just-check --strict-bitvector"
            f" --ddump-tc-ast pass/{filename} 1> rtpass/{filename}"
        )
        step(
            f"'{self.sail}' --no-memo-z3 --just-check --strict-bitvector"
            f" --ddump-tc-ast --dallow-internal rtpass/{filename} 1> rtpass2/{filename}"
        )
        step(f"diff rtpass/{filename} rtpass2/{filename}")
        variantdir = os.path.join("pass", basename)
        for variantname in os.listdir(variantdir) if os.path.isdir(variantdir) else []:
            if variantname.endswith(".sail"):
                variantbasename = os.path.splitext(os.path.basename(variantname))[0]
                step(
                    f"'{self.sail}' --no-memo-z3 --strict-bitvector"
                    f" pass/{basename}/{variantname} 2> pass/{basename}/{variantbasename}.error",
                    expected_status=1,
                )
                step(
                    f"diff pass/{basename}/{variantbasename}.error"
                    f" pass/{basename}/{variantbasename}.expect"
                )
                step(f"rm pass/{basename}/{variantbasename}.error")


@suite("typecheck.project", _SUITE_DIR)
class TypecheckProjectTests(SailTest):
    def run(self):
        self.banner("Testing multi-file projects")
        self.run_tests(
            "projects",
            Batcher.projects(_PROJECT_DIR),
            self._test,
            testdir=_SUITE_DIR,
        )

    def _test(self, filename, basename):
        if filename.startswith("fail"):
            step(
                f"'{self.sail}' --no-memo-z3 --strict-bitvector project/{filename}"
                f" --all-modules 2> project/{basename}.error",
                expected_status=1,
            )
            step(f"diff project/{basename}.error project/{basename}.expect")
            step(f"rm project/{basename}.error")
        else:
            step(f"'{self.sail}' --no-memo-z3 project/{filename} --all-modules")


@suite("typecheck.fail", _SUITE_DIR)
class TypecheckFailTests(SailTest):
    def run(self):
        self.banner("Testing failing programs")
        self.run_tests("fail", Batcher(_FAIL_DIR), self._test, testdir=_SUITE_DIR)

    def _test(self, filename, basename):
        step(
            f"'{self.sail}' --no-memo-z3 --strict-bitvector fail/{filename}"
            f" 2> fail/{basename}.error",
            expected_status=1,
        )
        step(f"diff fail/{basename}.error fail/{basename}.expect")
        step(f"rm fail/{basename}.error")
