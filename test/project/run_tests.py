#!/usr/bin/env python3

import os
import sys

os.environ["SAIL_NEW_CLI"] = "true"

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from sailtest import *

_SUITE_DIR = os.path.dirname(os.path.abspath(__file__))
_FAILURE_DIR = os.path.join(_SUITE_DIR, "failure")


class ProjectTests(SailTest):
    def run(self):
        self.banner("Testing project")
        self.run_tests(
            "project", os.listdir(_FAILURE_DIR), self._test, testdir=_SUITE_DIR
        )

    def _test(self, filename, basename):
        step(
            f"'{self.sail}' failure/{filename} 2> failure/{basename}.error",
            expected_status=1,
        )
        step(f"diff failure/{basename}.expect failure/{basename}.error")
        step(f"rm failure/{basename}.error")


ProjectTests().main(xml_dir=_SUITE_DIR)
