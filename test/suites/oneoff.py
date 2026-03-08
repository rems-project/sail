#!/usr/bin/env python3

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from sailtest import *

_TEST_DIR = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
_SUITE_DIR = os.path.join(_TEST_DIR, "oneoff")


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


OneoffTests().main(xml_dir=_SUITE_DIR)
