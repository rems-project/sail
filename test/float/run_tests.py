#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *


class FloatTests(SailTest):
    def run(self):
        self.banner(
            "Testing floating point c optimized with C options: -O2 Sail options: "
        )
        # Only files ending in _test are actual tests
        test_files = [
            f for f in os.listdir(".") if os.path.splitext(f)[0].endswith("_test")
        ]
        self.run_tests("floating point c optimized", test_files, self._test)

    def _test(self, filename, basename):
        step(f"'{self.sail}' -no_warn -c {filename} -o {basename}")
        step(
            f"cc -O2 {basename}.c '{self.sail_dir}'/lib/*.c -lgmp -I '{self.sail_dir}'/lib -o {basename}.bin"
        )
        step(
            f"./{basename}.bin > {basename}.result 2> {basename}.err_result",
            expected_status=1 if basename.startswith("fail") else 0,
        )
        step(f"diff {basename}.err_result no_error && rm {basename}.err_result")
        step(f"rm {basename}.c {basename}.h {basename}.bin {basename}.result")


FloatTests().main()
