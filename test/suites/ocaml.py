import os
import sys


from sailtest import *

_TEST_DIR = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
)
_SUITE_DIR = os.path.join(_TEST_DIR, "ocaml")


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

    def _test(self, dir, basename):
        step(
            f"{self.sail} --strict-bitvector --no-warn -o out --ocaml {self._opts} ../prelude.sail *.sail",
            cwd=dir,
        )
        step(
            "dune exec --release out > ../result 2> /dev/null", cwd=f"{dir}/_sbuild"
        )
        step("diff expect result", cwd=dir)
        step("rm result", cwd=dir)
        step("rm -rf _sbuild", cwd=dir)


@suite("ocaml.default", _SUITE_DIR)
class OcamlTests(_OcamlBase):
    pass


@suite("ocaml.trace", _SUITE_DIR)
class OcamlTraceTests(_OcamlBase):
    _opts = "--ocaml-trace"
