import os
import sys
import shutil


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "float")


@suite("float")
class FloatTests(SailTest):
    def prepare(self):
        shutil.copy(os.path.join(_SUITE_DIR, "data.sail"), os.path.join(self.work_dir, "data.sail"))
        shutil.copy(os.path.join(_SUITE_DIR, "tuple_equality.sail"), os.path.join(self.work_dir, "tuple_equality.sail"))

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
        )

    def _test(self, test):
        test.copy_filename()
        step(f"'{self.sail}' --no-warn -c {test.filename} -o {test.basename}")
        step(
            f"cc -O2 {test.basename}.c '{self.sail_dir}'/lib/*.c -lgmp -I '{self.sail_dir}'/lib -o {test.basename}.bin"
        )
        step(
            f"./{test.basename}.bin > {test.basename}.result 2> {test.basename}.err_result",
            expected_status=1 if test.basename.startswith("fail") else 0,
        )
        step(f"diff {test.basename}.err_result {test.directory}/no_error && rm {test.basename}.err_result")
