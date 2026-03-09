import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "project")
_FAILURE_DIR = os.path.join(_SUITE_DIR, "failure")


@suite("project")
class ProjectTests(SailTest):
    def run(self):
        self.banner("Testing project")
        self.run_tests("project", Batcher(_FAILURE_DIR), self._test)

    def _test(self, test):
        os.chdir(_SUITE_DIR)
        step(
            f"'{self.sail}' failure/{test.filename} 2> {self.work_dir}/{test.basename}.error",
            expected_status=1,
            env={"SAIL_NEW_CLI": "true"},
        )
        status = step_with_status(
            f"diff failure/{test.basename}.expect {self.work_dir}/{test.basename}.error"
        )
        if status != 0:
            if args.update_expected:
                print(f"Overriding file {test.basename}.expect")
                step(
                    f"'{self.sail}' failure/{test.filename} 2> failure/{test.basename}.expect",
                    expected_status=1,
                    env={"SAIL_NEW_CLI": "true"},
                )
            else:
                sys.exit(1)
