#!/usr/bin/env python3

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from sailtest import *

_TEST_DIR = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
_SUITE_DIR = os.path.join(_TEST_DIR, "lexing")


class LexingTests(SailTest):
    def run(self):
        self.banner("Testing lexer")
        self.run_tests("lex", Batcher(_SUITE_DIR), self._test, testdir=_SUITE_DIR)

    def _test(self, filename, basename):
        step(f"'{self.sail}' {filename} 2> {basename}.error", expected_status=1)
        step(f"diff {basename}.expect {basename}.error")
        step(f"rm {basename}.error")


LexingTests().main(xml_dir=_SUITE_DIR)
