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
        step(f"'{self.sail}' {filename} 2> {basename}.error", expected_status=1)
        step(f"diff {basename}.expect {basename}.error")
        step(f"rm {basename}.error")


LexingTests().main()
