#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *


class PatternCompletenessTests(SailTest):
    def run(self):
        self.banner("Testing pattern completeness checker")
        self.run_tests("completeness", os.listdir("."), self._test)

    def _test(self, filename, basename):
        step("'{}' --just-check {} 2> {}.error".format(self.sail, filename, basename))
        if filename.startswith("warn"):
            status = step_with_status(
                "diff {}.error {}.expect".format(basename, basename)
            )
        else:
            status = step_with_status("diff {}.error no_error".format(basename))
        if status != 0:
            if args.update_expected and filename.startswith("warn"):
                print(f"Overriding file {basename}.expected")
                step(f"'{self.sail}' --just-check {filename} 2> {basename}.expect")
            else:
                sys.exit(1)
        step("rm {}.error".format(basename))


PatternCompletenessTests().main()
