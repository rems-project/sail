#!/usr/bin/env python3

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from sailtest import *

_TEST_DIR = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
_SUITE_DIR = os.path.join(_TEST_DIR, "ocaml")


class OcamlTests(SailTest):
    def run(self):
        targets = self.get_targets(["ocaml", "ocaml_trace"])
        print(f"Targets: {targets}")

        if "ocaml" in targets:
            opts = ""
            self.banner(f'Ocaml testing with options: "{opts}"')
            self.run_tests(
                "Ocaml testing",
                os.listdir(_SUITE_DIR),
                self._make_test(opts),
                testdir=_SUITE_DIR,
                chunks_fn=directory_chunks,
            )

        if "ocaml_trace" in targets:
            opts = "--ocaml-trace"
            self.banner(f'Ocaml trace testing with options: "{opts}"')
            self.run_tests(
                "Ocaml trace testing",
                os.listdir(_SUITE_DIR),
                self._make_test(opts),
                testdir=_SUITE_DIR,
                chunks_fn=directory_chunks,
            )

    def _make_test(self, opts):
        def fn(dir, basename):
            step(
                f"{self.sail} --strict-bitvector --no-warn -o out --ocaml {opts} ../prelude.sail *.sail",
                cwd=dir,
            )
            step(
                "dune exec --release out > ../result 2> /dev/null", cwd=f"{dir}/_sbuild"
            )
            step("diff expect result", cwd=dir)
            step("rm result", cwd=dir)
            step("rm -rf _sbuild", cwd=dir)

        return fn


OcamlTests().main(xml_dir=_SUITE_DIR)
