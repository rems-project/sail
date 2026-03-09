import os
import sys

os.environ["SAIL_NEW_CLI"] = "true"


from sailtest import *

_TEST_DIR = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
)
_SUITE_DIR = os.path.join(_TEST_DIR, "project")
_FAILURE_DIR = os.path.join(_SUITE_DIR, "failure")


@suite("project", _SUITE_DIR)
class ProjectTests(SailTest):
    def run(self):
        self.banner("Testing project")
        self.run_tests("project", Batcher(_FAILURE_DIR), self._test, testdir=_SUITE_DIR)

    def _test(self, filename, basename):
        step(
            f"'{self.sail}' failure/{filename} 2> failure/{basename}.error",
            expected_status=1,
        )
        step(f"diff failure/{basename}.expect failure/{basename}.error")
        step(f"rm failure/{basename}.error")
