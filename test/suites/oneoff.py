import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "oneoff")


@suite("oneoff")
class OneoffTests(SailTest):
    def run(self):
        self.banner("Testing")
        self.run_tests(
            "one-off",
            Batcher.directories(_SUITE_DIR),
            self._test,
            testdir=_SUITE_DIR,
        )

    def _test(self, test):
        os.chdir(test.path)
        step("./test.sh", name=test.filename)
