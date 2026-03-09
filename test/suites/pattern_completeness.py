import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "pattern_completeness")


@suite("pattern_completeness", _SUITE_DIR)
class PatternCompletenessTests(SailTest):
    def run(self):
        self.banner("Testing pattern completeness checker")
        self.run_tests(
            "completeness", Batcher(_SUITE_DIR), self._test, testdir=_SUITE_DIR
        )

    def _test(self, test):
        step(f"'{self.sail}' --just-check {test.filename} 2> {test.basename}.error")
        if test.filename.startswith("warn"):
            status = step_with_status(f"diff {test.basename}.error {test.basename}.expect")
        else:
            status = step_with_status(f"diff {test.basename}.error no_error")
        if status != 0:
            if args.update_expected and test.filename.startswith("warn"):
                print(f"Overriding file {test.basename}.expected")
                step(f"'{self.sail}' --just-check {test.filename} 2> {test.basename}.expect")
            else:
                sys.exit(1)
        step(f"rm {test.basename}.error")
