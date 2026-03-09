import os
import sys


from sailtest import *

_TEST_DIR = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
)
_SUITE_DIR = os.path.join(_TEST_DIR, "float")


@suite("float", _SUITE_DIR)
class FloatTests(SailTest):
    def run(self):
        self.banner(
            "Testing floating point c optimized with C options: -O2 Sail options: "
        )
        self.run_tests(
            "floating point c optimized",
            Batcher(
                _SUITE_DIR,
                predicate=lambda f: sail_file(f)
                and os.path.splitext(f)[0].endswith("_test"),
            ),
            self._test,
            testdir=_SUITE_DIR,
        )

    def _test(self, filename, basename):
        step(f"'{self.sail}' -no_warn -c {filename} -o {basename}")
        step(
            f"cc -O2 {basename}.c '{self.sail_dir}'/lib/*.c -lgmp -I '{self.sail_dir}'/lib -o {basename}.bin"
        )
        step(
            f"./{basename}.bin > {basename}.result 2> {basename}.err_result",
            expected_status=1 if basename.startswith("fail") else 0,
        )
        step(f"diff {basename}.err_result no_error && rm {basename}.err_result")
        step(f"rm {basename}.c {basename}.h {basename}.bin {basename}.result")
