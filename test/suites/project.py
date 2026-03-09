import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "project")
_FAILURE_DIR = os.path.join(_SUITE_DIR, "failure")


@suite("project", _SUITE_DIR)
class ProjectTests(SailTest):
    def run(self):
        self.banner("Testing project")
        self.run_tests("project", Batcher(_FAILURE_DIR), self._test, testdir=_SUITE_DIR)

    def _test(self, test):
        step(
            f"'{self.sail}' failure/{test.filename} 2> failure/{test.basename}.error",
            expected_status=1,
            env={"SAIL_NEW_CLI": "true"},
        )
        step(f"diff failure/{test.basename}.expect failure/{test.basename}.error")
        step(f"rm failure/{test.basename}.error")
