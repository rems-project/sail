import os
import sys
from shutil import which


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "typecheck")
_PASS_DIR = os.path.join(_SUITE_DIR, "pass")
_PROJECT_DIR = os.path.join(_SUITE_DIR, "project")
_FAIL_DIR = os.path.join(_SUITE_DIR, "fail")


@suite("typecheck.pass", work_dir="tcpass")
class TypecheckPassTests(SailTest):
    def run(self):
        os.makedirs(os.path.join(self.work_dir, "_rtpass"), exist_ok=True)
        os.makedirs(os.path.join(self.work_dir, "_rtpass2"), exist_ok=True)

        skip_pass = set()
        if which("cvc4") is None:
            skip_pass.add("type_pow_zero")

        self.banner("Testing passing programs")
        self.run_tests(
            "pass",
            Batcher(_PASS_DIR),
            self._test,
            skip_set=skip_pass,
        )

    def _test(self, test):
        test.copy_filename()
        step(
            f"'{self.sail}' --no-memo-z3 --just-check --strict-bitvector"
            f" --ddump-tc-ast {test.filename} 1> _rtpass/{test.filename}"
        )
        step(
            f"'{self.sail}' --no-memo-z3 --just-check --strict-bitvector"
            f" --ddump-tc-ast --dallow-internal _rtpass/{test.filename} 1> _rtpass2/{test.filename}"
        )
        step(f"diff _rtpass/{test.filename} _rtpass2/{test.filename}")
        variant_dir = os.path.join(test.directory, test.basename)
        if os.path.isdir(variant_dir):
            os.makedirs(os.path.join(self.work_dir, test.basename), exist_ok=True)
            variant_work_dir = os.path.join(self.work_dir, test.basename)
            for variant_name in (
                os.listdir(variant_dir) if os.path.isdir(variant_dir) else []
            ):
                if not variant_name.endswith(".sail"):
                    continue
                variant_basename = os.path.splitext(os.path.basename(variant_name))[0]
                variant_work_path = os.path.join(variant_work_dir, variant_name)
                shutil.copy(os.path.join(variant_dir, variant_name), variant_work_path)
                step(
                    f"'{self.sail}' --no-memo-z3 --strict-bitvector"
                    f" {test.basename}/{variant_name} 2> {test.basename}/{variant_basename}.error",
                    expected_status=1,
                )
                status = step_with_status(
                    f"diff {test.basename}/{variant_basename}.error"
                    f" {variant_dir}/{variant_basename}.expect"
                )
                if status != 0:
                    if args.update_expected:
                        print(f"Overriding file {test.expect}")
                        step(
                            f"'{self.sail}' --no-memo-z3 --strict-bitvector"
                            f" {test.basename}/{variant_name} 2> {variant_dir}/{variant_basename}.expect",
                            expected_status=1,
                        )
                    else:
                        sys.exit(1)


@suite("typecheck.project", work_dir="tcproj")
class TypecheckProjectTests(SailTest):
    def run(self):
        self.banner("Testing multi-file projects")
        self.run_tests(
            "projects",
            Batcher.projects(_PROJECT_DIR),
            self._test,
        )

    def _test(self, test):
        if test.filename.startswith("fail"):
            os.chdir(test.directory)
            step(
                f"'{self.sail}' --no-memo-z3 --strict-bitvector {test.filename}"
                f" --all-modules 2> {self.work_dir}/{test.error}",
                expected_status=1,
            )
            status = step_with_status(
                f"diff {self.work_dir}/{test.error} {test.expect}"
            )
            if status != 0:
                if args.update_expected:
                    print(f"Overriding file {test.expect}")
                    step(
                        f"'{self.sail}' --no-memo-z3 --strict-bitvector"
                        f" {test.filename} --all-modules 2> {test.expect}",
                        expected_status=1,
                    )
                else:
                    sys.exit(1)
        else:
            step(f"'{self.sail}' --no-memo-z3 {test.path} --all-modules")


@suite("typecheck.fail", work_dir="tcfail")
class TypecheckFailTests(SailTest):
    def run(self):
        self.banner("Testing failing programs")
        self.run_tests("fail", Batcher(_FAIL_DIR), self._test)

    def _test(self, test):
        test.copy_filename()
        step(
            f"'{self.sail}' --no-memo-z3 --strict-bitvector {test.filename}"
            f" 2> {test.basename}.error",
            expected_status=1,
        )
        status = step_with_status(f"diff {test.basename}.error {test.expect}")
        if status != 0:
            if args.update_expected:
                print(f"Overriding file {test.expect}")
                step(
                    f"'{self.sail}' --no-memo-z3 --strict-bitvector {test.filename} 2> {test.expect}",
                    expected_status=1,
                )
            else:
                sys.exit(1)
