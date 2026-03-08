#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *


class OneoffTests(SailTest):
    def run(self):
        banner("Testing")
        self.run_tests(
            "one-off", os.listdir("."), self._test, chunks_fn=directory_chunks
        )

    def _test(self, dir, basename):
        os.chdir(dir)
        step("./test.sh", name=dir)


OneoffTests().main()
