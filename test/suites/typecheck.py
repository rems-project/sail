import os
import sys
from shutil import which


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "typecheck")
_PASS_DIR = os.path.join(_SUITE_DIR, "pass")
_PROJECT_DIR = os.path.join(_SUITE_DIR, "project")
_FAIL_DIR = os.path.join(_SUITE_DIR, "fail")


@suite("typecheck.pass")
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

    def _test(self, test):
        step(
            f"'{self.sail}' --no-memo-z3 --just-check --strict-bitvector"
            f" --ddump-tc-ast pass/{test.filename} 1> rtpass/{test.filename}"
        )
        step(
            f"'{self.sail}' --no-memo-z3 --just-check --strict-bitvector"
            f" --ddump-tc-ast --dallow-internal rtpass/{test.filename} 1> rtpass2/{test.filename}"
        )
        step(f"diff rtpass/{test.filename} rtpass2/{test.filename}")
        variantdir = os.path.join("pass", test.basename)
        for variantname in os.listdir(variantdir) if os.path.isdir(variantdir) else []:
            if variantname.endswith(".sail"):
                variantbasename = os.path.splitext(os.path.basename(variantname))[0]
                step(
                    f"'{self.sail}' --no-memo-z3 --strict-bitvector"
                    f" pass/{test.basename}/{variantname} 2> pass/{test.basename}/{variantbasename}.error",
                    expected_status=1,
                )
                step(
                    f"diff pass/{test.basename}/{variantbasename}.error"
                    f" pass/{test.basename}/{variantbasename}.expect"
                )
                step(f"rm pass/{test.basename}/{variantbasename}.error")


@suite("typecheck.project")
class TypecheckProjectTests(SailTest):
    def run(self):
        self.banner("Testing multi-file projects")
        self.run_tests(
            "projects",
            Batcher.projects(_PROJECT_DIR),
            self._test,
            testdir=_SUITE_DIR,
        )

    def _test(self, test):
        if test.filename.startswith("fail"):
            step(
                f"'{self.sail}' --no-memo-z3 --strict-bitvector project/{test.filename}"
                f" --all-modules 2> project/{test.basename}.error",
                expected_status=1,
            )
            step(f"diff project/{test.basename}.error project/{test.basename}.expect")
            step(f"rm project/{test.basename}.error")
        else:
            step(f"'{self.sail}' --no-memo-z3 project/{test.filename} --all-modules")


@suite("typecheck.fail")
class TypecheckFailTests(SailTest):
    def run(self):
        self.banner("Testing failing programs")
        self.run_tests("fail", Batcher(_FAIL_DIR), self._test, testdir=_SUITE_DIR)

    def _test(self, test):
        step(
            f"'{self.sail}' --no-memo-z3 --strict-bitvector fail/{test.filename}"
            f" 2> fail/{test.basename}.error",
            expected_status=1,
        )
        step(f"diff fail/{test.basename}.error fail/{test.basename}.expect")
        step(f"rm fail/{test.basename}.error")
