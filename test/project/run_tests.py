#!/usr/bin/env python3

import os
import sys

os.environ["SAIL_NEW_CLI"] = "true"

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *


class ProjectTests(SailTest):
    def run(self):
        self.banner("Testing project")
        self.run_tests("project", os.listdir("failure"), self._test)

    def _test(self, filename, basename):
        step(
            f"'{self.sail}' failure/{filename} 2> failure/{basename}.error",
            expected_status=1,
        )
        step(f"diff failure/{basename}.expect failure/{basename}.error")
        step(f"rm failure/{basename}.error")


ProjectTests().main()
