#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *

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
joiner = " "
libpaths = joiner.join(
    ["{}/src/gen_lib/sail2_{}.lem".format("{}", lib) for lib in libraries]
)
libml = joiner.join(["sail2_{}.ml".format(lib) for lib in libraries])


def _mono_chunks(filenames, cores):
    """Custom chunking for mono tests: files in pass/ have no extension and aren't .sail files."""
    ys = []
    chunk = []
    for filename in filenames:
        if not args.test or filename in args.test:
            chunk.append(filename)
        if len(chunk) >= cores:
            ys.append(list(chunk))
            chunk = []
    ys.append(list(chunk))
    return ys


class MonoTests(SailTest):
    def run(self):
        self.banner("Monomorphisation tests")
        self.run_tests("mono", os.listdir("pass"), self._test, chunks_fn=_mono_chunks)

    def _test(self, filename, basename):
        with open("pass/{}".format(filename)) as f:
            arguments = f.read()
        step("mkdir -p _build_{}".format(filename))
        step(
            "'{}' --lem --lem-mwords --lem-lib Test_extra --lem-output-dir _build_{} -o out {}".format(
                self.sail, filename, arguments
            )
        )
        os.chdir("_build_{}".format(filename))
        step(
            "lem -ocaml -lib {}/src/lem_interp {} -outdir . ../test_extra.lem out_types.lem out.lem".format(
                self.sail_dir, libpaths.format(self.sail_dir)
            )
        )
        step(
            "if grep -q initial_regstate out.lem; then cp ../test_with_state.ml test.ml; else cp ../test.ml test.ml; fi"
        )
        step(
            "ocamlfind ocamlc -linkpkg -package zarith -package lem {} test_extra.ml out_types.ml out.ml test.ml".format(
                libml
            )
        )
        os.chdir("..")
        step("rm -r _build_{}".format(filename))


MonoTests().main()
