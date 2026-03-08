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
            "'{}' failure/{} 2> failure/{}.error".format(self.sail, filename, basename),
            expected_status=1,
        )
        step("diff failure/{}.expect failure/{}.error".format(basename, basename))
        step("rm failure/{}.error".format(basename))


ProjectTests().main()
