import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "oneoff")


@suite("oneoff", _SUITE_DIR)
class OneoffTests(SailTest):
    def run(self):
        self.banner("Testing")
        self.run_tests(
            "one-off",
            Batcher.directories(_SUITE_DIR),
            self._test,
            testdir=_SUITE_DIR,
        )

    def _test(self, dir, basename):
        os.chdir(dir)
        step("./test.sh", name=dir)
