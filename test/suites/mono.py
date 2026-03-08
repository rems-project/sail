#!/usr/bin/env python3

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from sailtest import *

_TEST_DIR = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
_SUITE_DIR = os.path.join(_TEST_DIR, "mono")
_PASS_DIR = os.path.join(_SUITE_DIR, "pass")

libraries = [
    "values",
    "operators",
    "instr_kinds",
    "prompt_monad",
    "prompt",
    "operators_mwords",
    "state_monad",
    "state",
    "string",
    "undefined",
]
libml = " ".join(f"sail2_{lib}.ml" for lib in libraries)


class MonoTests(SailTest):
    def run(self):
        self.banner("Monomorphisation tests")
        self.run_tests(
            "mono",
            Batcher(_PASS_DIR, predicate=lambda f: not args.test or os.path.basename(f) in args.test),
            self._test,
            testdir=_SUITE_DIR,
        )

    def _test(self, filename, basename):
        libpaths = " ".join(
            f"{self.sail_dir}/src/gen_lib/sail2_{lib}.lem" for lib in libraries
        )
        with open(f"pass/{filename}") as f:
            arguments = f.read()
        step(f"mkdir -p _build_{filename}")
        step(
            f"'{self.sail}' --lem --lem-mwords --lem-lib Test_extra"
            f" --lem-output-dir _build_{filename} -o out {arguments}"
        )
        os.chdir(f"_build_{filename}")
        step(
            f"lem -ocaml -lib {self.sail_dir}/src/lem_interp {libpaths}"
            f" -outdir . ../test_extra.lem out_types.lem out.lem"
        )
        step(
            "if grep -q initial_regstate out.lem; then cp ../test_with_state.ml test.ml; else cp ../test.ml test.ml; fi"
        )
        step(
            f"ocamlfind ocamlc -linkpkg -package zarith -package lem"
            f" {libml} test_extra.ml out_types.ml out.ml test.ml"
        )
        os.chdir("..")
        step(f"rm -r _build_{filename}")


MonoTests().main(xml_dir=_SUITE_DIR)
