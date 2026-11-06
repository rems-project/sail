import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "format")


@suite("format", _SUITE_DIR)
class FormatTests(SailTest):
    def run(self):
        self.banner("Testing default")
        self.run_tests(
            "default",
            Batcher(_SUITE_DIR),
            self._make_test("default"),
            testdir=_SUITE_DIR,
        )

        self.banner("Testing lw80_preserve")
        self.run_tests(
            "lw80_preserve",
            Batcher(_SUITE_DIR),
            self._make_test("lw80_preserve"),
            testdir=_SUITE_DIR,
        )

    def _make_test(self, test_dir):
        def fn(filename, basename):
            step(f"cp {filename} {test_dir}/{filename}")
            step(
                f"'{self.sail}' --sail-config {test_dir}/config.json --fmt {test_dir}/{filename}"
            )
            status = step_with_status(
                f"diff {test_dir}/{filename} {test_dir}/{basename}.expect"
            )
            if status != 0:
                if args.update_expected:
                    print(f"Overriding file {test_dir}/{basename}.expected")
                    step(
                        f"'{self.sail}' --sail-config {test_dir}/config.json --fmt {filename} --fmt-emit stdout > {test_dir}/{basename}.expect"
                    )
                else:
                    sys.exit(1)
            step(f"rm {test_dir}/{filename}")

        return fn
