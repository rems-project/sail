#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *


class FloatTests(SailTest):
    def run(self):
        banner("Testing floating point c optimized with C options: -O2 Sail options: ")
        # Only files ending in _test are actual tests
        test_files = [
            f for f in os.listdir(".") if os.path.splitext(f)[0].endswith("_test")
        ]
        self.run_tests("floating point c optimized", test_files, self._test)

    def _test(self, filename, basename):
        step("'{}' -no_warn -c {} -o {}".format(self.sail, filename, basename))
        step(
            "cc -O2 {}.c '{}'/lib/*.c -lgmp -I '{}'/lib -o {}.bin".format(
                basename, self.sail_dir, self.sail_dir, basename
            )
        )
        step(
            "./{}.bin > {}.result 2> {}.err_result".format(
                basename, basename, basename
            ),
            expected_status=1 if basename.startswith("fail") else 0,
        )
        step(
            "diff {}.err_result no_error && rm {}.err_result".format(basename, basename)
        )
        step(
            "rm {}.c {}.h {}.bin {}.result".format(
                basename, basename, basename, basename
            )
        )


FloatTests().main()
