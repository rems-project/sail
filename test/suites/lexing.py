import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "lexing")


@suite("lexing")
class LexingTests(SailTest):
    def run(self):
        self.banner("Testing lexer")
        self.run_tests("lex", Batcher(_SUITE_DIR), self._test)

    def _test(self, test):
        test.copy_filename()
        step(f"'{self.sail}' {test.filename} 2> {test.error}", expected_status=1)
        step(f"diff {test.expect} {test.error}")
