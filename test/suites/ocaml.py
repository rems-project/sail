import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "ocaml")


class _OcamlBase(SailTest):
    """Shared test logic for OCaml sub-suites. Not registered."""

    _opts = ""

    def run(self):
        self.banner(f'Ocaml testing with options: "{self._opts}"')
        self.run_tests(
            "Ocaml testing",
            Batcher.directories(_SUITE_DIR),
            self._test,
            testdir=_SUITE_DIR,
        )

    def _test(self, test):
        step(
            f"{self.sail} --strict-bitvector --no-warn -o out --ocaml {self._opts} ../prelude.sail *.sail",
            cwd=test.path,
        )
        step(
            "dune exec --release out > ../result 2> /dev/null", cwd=f"{test.path}/_sbuild"
        )
        step("diff expect result", cwd=test.path)
        step("rm result", cwd=test.path)
        step("rm -rf _sbuild", cwd=test.path)


@suite("ocaml.default", work_dir="ocaml")
class OcamlTests(_OcamlBase):
    pass


@suite("ocaml.trace", work_dir="ocaml_trace")
class OcamlTraceTests(_OcamlBase):
    _opts = "--ocaml-trace"
