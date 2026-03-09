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
        )

    def _test(self, test):
        test.copy_directory()
        os.chdir(test.filename)
        step("./test.sh", name=test.filename)
