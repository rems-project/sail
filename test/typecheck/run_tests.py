#!/usr/bin/env python3

import os
import sys
from shutil import which

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *


class TypecheckTests(SailTest):
    def run(self):
        step("mkdir -p rtpass")
        step("mkdir -p rtpass2")

        skip_pass = set()
        if which("cvc4") is None:
            skip_pass.add("type_pow_zero")

        self.banner("Testing passing programs")
        self.run_tests("pass", os.listdir("pass"), self._test_pass, skip_set=skip_pass)

        self.banner("Testing multi-file projects")
        self.run_tests(
            "projects",
            os.listdir("project"),
            self._test_project,
            chunks_fn=project_chunks,
        )

        self.banner("Testing failing programs")
        self.run_tests("fail", os.listdir("fail"), self._test_fail)

    def _test_pass(self, filename, basename):
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

    def _test_project(self, filename, basename):
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

    def _test_fail(self, filename, basename):
        step(
            f"'{self.sail}' --no-memo-z3 --strict-bitvector fail/{filename}"
            f" 2> fail/{basename}.error",
            expected_status=1,
        )
        step(f"diff fail/{basename}.error fail/{basename}.expect")
        step(f"rm fail/{basename}.error")


TypecheckTests().main()
