#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.join(mydir, ".."))

from sailtest import *


class BuiltinsTests(SailTest):
    def run(self):
        targets = self.get_targets(["c", "ocaml"])
        print("Targets: {}".format(targets))

        if "c" in targets:
            self.banner("Testing builtins: C, No optimisations Sail options: ")
            self.run_tests(
                "C, No optimisations", os.listdir("."), self._make_c_test("")
            )

            self.banner("Testing builtins: C, Optimisations Sail options: -O")
            self.run_tests("C, Optimisations", os.listdir("."), self._make_c_test("-O"))

            self.banner(
                "Testing builtins: C, Constant folding Sail options: -Oconstant_fold"
            )
            self.run_tests(
                "C, Constant folding",
                os.listdir("."),
                self._make_c_test("-Oconstant_fold"),
            )

        if "ocaml" in targets:
            self.banner("Testing builtins: OCaml Sail options: ")
            self.run_tests("OCaml", os.listdir("."), self._test_ocaml)

        if "lem" in targets:
            self.banner("Testing builtins: Lem to OCaml")
            self.run_tests("Lem to OCaml", os.listdir("."), self._test_lem)

        if "coq" in targets:
            self.banner("Testing builtins: Coq")
            self.run_tests("Coq", os.listdir("."), self._test_coq)

        if "isla" in targets:
            self.banner("Testing builtins: Isla")
            self.run_tests("Isla", os.listdir("."), self._test_isla)

    def _make_c_test(self, sail_opts):
        def fn(filename, basename):
            step(
                "'{}' -no_warn -c {} {} -o {}".format(
                    self.sail, sail_opts, filename, basename
                )
            )
            step(
                "gcc {}.c '{}'/lib/*.c -lgmp -I '{}'/lib -o {}".format(
                    basename, self.sail_dir, self.sail_dir, basename
                )
            )
            step("./{}".format(basename))
            step("rm {}.c".format(basename))
            step("rm {}.h".format(basename))
            step("rm {}".format(basename))

        return fn

    def _test_ocaml(self, filename, basename):
        step(
            "'{}' -no_warn -ocaml -ocaml_build_dir _sbuild_{} -o {} {}".format(
                self.sail, basename, basename, filename
            )
        )
        step("./{}".format(basename))
        step("rm -r _sbuild_{}".format(basename))
        step("rm {}".format(basename))

    def _test_lem(self, filename, basename):
        step("'{}' -no_warn -lem -o {} {}".format(self.sail, basename, filename))
        step("mkdir -p _lbuild_{}".format(basename))
        step("mv {}.lem _lbuild_{}".format(basename, basename))
        step("mv {}_types.lem _lbuild_{}".format(basename, basename))
        step("cp myocamlbuild.ml _lbuild_{}".format(basename))
        step("cp '{}'/src/gen_lib/*.lem _lbuild_{}".format(self.sail_dir, basename))
        os.chdir("_lbuild_{}".format(basename))
        step("ocamlbuild -package lem {}.native".format(basename))
        step("./{}.native".format(basename))
        os.chdir("..")
        step("rm -r _lbuild_{}".format(basename))

    def _test_coq(self, filename, basename):
        step(
            "'{}' --no-warn --coq --coq-lib-style stdpp --coq-record-update --undefined-gen -o {} {}".format(
                self.sail, basename, filename
            )
        )
        step("mkdir -p _coqbuild_{}".format(basename))
        step("mv {}.v _coqbuild_{}".format(basename, basename))
        step("mv {}_types.v _coqbuild_{}".format(basename, basename))
        step("cp test.v _coqbuild_{}".format(basename))
        os.chdir("_coqbuild_{}".format(basename))
        step("coqc {}_types.v".format(basename))
        step("coqc {}.v".format(basename))
        step(
            "coqtop -require-import {}_types -require-import {} -l test.v -batch | tee /dev/stderr | grep -q OK".format(
                basename, basename
            )
        )
        os.chdir("..")
        step("rm -r _coqbuild_{}".format(basename))

    def _test_isla(self, filename, basename):
        isla_dir = os.environ["ISLA_DIR"]
        step(
            "'{}'/isla-sail/isla-sail {} '{}'/lib/vector_dec.sail '{}'/test/property/include/config.sail -o {}".format(
                isla_dir, filename, self.sail_dir, isla_dir, basename
            )
        )
        step(
            "'{}'/target/release/isla-execute-function -A {}.ir -C '{}'/configs/plain.toml main".format(
                isla_dir, basename, isla_dir
            )
        )
        step("rm {}.ir".format(basename))


BuiltinsTests().main()
