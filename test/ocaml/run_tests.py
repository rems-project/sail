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
            opts = ""
            self.banner(f'Ocaml testing with options: "{opts}"')
            self.run_tests(
                "Ocaml testing",
                os.listdir("."),
                self._make_test(opts),
                chunks_fn=directory_chunks,
            )

        if "ocaml_trace" in targets:
            opts = "--ocaml-trace"
            self.banner(f'Ocaml trace testing with options: "{opts}"')
            self.run_tests(
                "Ocaml trace testing",
                os.listdir("."),
                self._make_test(opts),
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
