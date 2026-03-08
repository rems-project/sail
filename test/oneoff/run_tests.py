#!/usr/bin/env python3

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from sailtest import *

_SUITE_DIR = os.path.dirname(os.path.abspath(__file__))


class OneoffTests(SailTest):
    def run(self):
        self.banner("Testing")
        self.run_tests(
            "one-off",
            os.listdir(_SUITE_DIR),
            self._test,
            testdir=_SUITE_DIR,
            chunks_fn=directory_chunks,
        )

    def _test(self, dir, basename):
        os.chdir(dir)
        step("./test.sh", name=dir)


OneoffTests().main(xml_dir=_SUITE_DIR)
