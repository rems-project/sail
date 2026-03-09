import os
import sys


from sailtest import *


class _FormatTests(SailTest):
    def run_with_dir(self, dir):
        self.banner(f"Testing {dir}")
        self.run_tests(
            dir,
            Batcher(os.path.join(TEST_DIR, "format")),
            self._make_test(dir),
        )

    def _make_test(self, test_dir):
        def fn(test):
            config = f"{test.directory}/{test_dir}/config.json"
            expect = f"{test.directory}/{test_dir}/{test.basename}.expect"
            test.copy_filename()
            step(f"'{self.sail}' --sail-config {config} --fmt {test.filename}")
            status = step_with_status(f"diff {test.filename} {expect}")
            if status != 0:
                if args.update_expected:
                    print(f"Overriding file {expect}")
                    step(
                        f"'{self.sail}' --sail-config {config} --fmt {test.filename} --fmt-emit stdout > {expect}"
                    )
                else:
                    sys.exit(1)

        return fn


@suite("format.default")
class FormatDefaultTests(_FormatTests):
    def run(self):
        self.run_with_dir("default")


@suite("format.lw80_preserve")
class FormatLw80PreserveTests(_FormatTests):
    def run(self):
        self.run_with_dir("lw80_preserve")
