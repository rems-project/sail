#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *


class FormatTests(SailTest):
    def run(self):
        self.banner("Testing default")
        self.run_tests("default", os.listdir("."), self._make_test("default"))

        self.banner("Testing lw80_preserve")
        self.run_tests(
            "lw80_preserve", os.listdir("."), self._make_test("lw80_preserve")
        )

    def _make_test(self, test_dir):
        def fn(filename, basename):
            step(f"cp {filename} {test_dir}/{filename}")
            step(
                f"'{self.sail}' --sail-config {test_dir}/config.json --fmt {test_dir}/{filename}"
            )
            status = step_with_status(
                f"diff {test_dir}/{filename} {test_dir}/{basename}.expect"
            )
            if status != 0:
                if args.update_expected:
                    print(f"Overriding file {test_dir}/{basename}.expected")
                    step(
                        f"'{self.sail}' --sail-config {test_dir}/config.json --fmt {filename} --fmt-emit stdout > {test_dir}/{basename}.expect"
                    )
                else:
                    sys.exit(1)
            step(f"rm {test_dir}/{filename}")

        return fn


FormatTests().main()
