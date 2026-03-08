#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *


class OcamlTests(SailTest):
    def run(self):
        targets = self.get_targets(["ocaml", "ocaml_trace"])
        print("Targets: {}".format(targets))

        if "ocaml" in targets:
            self.banner('Ocaml testing with options: ""')
            self.run_tests(
                "Ocaml testing",
                os.listdir("."),
                self._make_test(""),
                chunks_fn=directory_chunks,
            )

        if "ocaml_trace" in targets:
            self.banner('Ocaml trace testing with options: "--ocaml-trace"')
            self.run_tests(
                "Ocaml trace testing",
                os.listdir("."),
                self._make_test("--ocaml-trace"),
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


OcamlTests().main()
