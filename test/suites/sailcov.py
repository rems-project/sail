#!/usr/bin/env python3

import os
import sys


from sailtest import *

_TEST_DIR = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
_SUITE_DIR = os.path.join(_TEST_DIR, "sailcov")


class SailcovTests(SailTest):
    def run(self):
        sailcov = f"{self.sail_dir}/sailcov/sailcov"
        self.banner("Testing sailcov")
        if not self._have_sailcov(sailcov):
            print("Skipping because no sailcov executable found")
            # Append an empty suite so tests.xml is still written
            self._xml_parts.append(Results("sailcov").finish())
            return
        self.run_tests(
            "sailcov", Batcher(_SUITE_DIR), self._make_test(sailcov), testdir=_SUITE_DIR
        )

    def _have_sailcov(self, sailcov):
        try:
            subprocess.call([sailcov, "--help"], stdout=subprocess.DEVNULL)
            return True
        except FileNotFoundError:
            return False

    def _make_test(self, sailcov):
        def fn(filename, basename):
            step(
                f"'{self.sail}' -no_warn -no_memo_z3 -c -c_include sail_coverage.h"
                f" -c_coverage {basename}.branches {filename} -o {basename}"
            )
            step(
                f"cc {basename}.c '{self.sail_dir}'/lib/*.c"
                f" '{self.sail_dir}'/lib/coverage/target/release/libsail_coverage.a"
                f" -lgmp -lpthread -ldl -I '{self.sail_dir}'/lib -o {basename}.bin"
            )
            step(f"./{basename}.bin -c {basename}.taken")
            step(
                f"'{sailcov}' --werror --all {basename}.branches"
                f" --taken {basename}.taken {filename}"
            )
            step(f"diff {basename}.html {basename}.expect")
            step(f"rm {basename}.taken {basename}.bin {basename}.branches")

        return fn


SailcovTests().main(xml_dir=_SUITE_DIR)
