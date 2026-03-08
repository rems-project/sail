#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *


class LexingTests(SailTest):
    def run(self):
        self.banner("Testing lexer")
        self.run_tests("lex", os.listdir("."), self._test)

    def _test(self, filename, basename):
        step(
            "'{}' {} 2> {}.error".format(self.sail, filename, basename),
            expected_status=1,
        )
        step("diff {}.expect {}.error".format(basename, basename))
        step("rm {}.error".format(basename))


LexingTests().main()
