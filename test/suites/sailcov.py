import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "sailcov")


@suite("sailcov")
class SailcovTests(SailTest):
    def run(self):
        sailcov = f"{self.sail_dir}/sailcov/sailcov"
        self.banner("Testing sailcov")
        if not self._have_sailcov(sailcov):
            print("Skipping because no sailcov executable found")
            # Append an empty suite so tests.xml is still written
            self._xml_parts.append(Results("sailcov").finish())
            return
        self.run_tests(
            "sailcov", Batcher(_SUITE_DIR), self._make_test(sailcov), testdir=_SUITE_DIR
        )

    def _have_sailcov(self, sailcov):
        try:
            subprocess.call([sailcov, "--help"], stdout=subprocess.DEVNULL)
            return True
        except FileNotFoundError:
            return False

    def _make_test(self, sailcov):
        def fn(test):
            step(
                f"'{self.sail}' -no_warn -no_memo_z3 -c -c_include sail_coverage.h"
                f" -c_coverage {test.basename}.branches {test.filename} -o {test.basename}"
            )
            step(
                f"cc {test.basename}.c '{self.sail_dir}'/lib/*.c"
                f" '{self.sail_dir}'/lib/coverage/target/release/libsail_coverage.a"
                f" -lgmp -lpthread -ldl -I '{self.sail_dir}'/lib -o {test.basename}.bin"
            )
            step(f"./{test.basename}.bin -c {test.basename}.taken")
            step(
                f"'{sailcov}' --werror --all {test.basename}.branches"
                f" --taken {test.basename}.taken {test.filename}"
            )
            step(f"diff {test.basename}.html {test.basename}.expect")
            step(f"rm {test.basename}.taken {test.basename}.bin {test.basename}.branches")

        return fn
