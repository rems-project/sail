import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "lexing")


@suite("lexing", _SUITE_DIR)
class LexingTests(SailTest):
    def run(self):
        self.banner("Testing lexer")
        self.run_tests("lex", Batcher(_SUITE_DIR), self._test, testdir=_SUITE_DIR)

    def _test(self, filename, basename):
        step(f"'{self.sail}' {filename} 2> {basename}.error", expected_status=1)
        step(f"diff {basename}.expect {basename}.error")
        step(f"rm {basename}.error")
