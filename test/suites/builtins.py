import os
import sys


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "builtins")


@suite("builtins.c")
class BuiltinsCTests(SailTest):
    def run(self):
        for name, sail_opts in [
            ("No optimisations", ""),
            ("Optimisations", "-O"),
            ("Constant folding", "-Oconstant_fold"),
        ]:
            self.banner(f"Testing builtins: C, {name} Sail options: {sail_opts}")
            self._run_c_tests(f"C, {name}", sail_opts)

    def _run_c_tests(self, name, sail_opts):
        def fn(test):
            step(
                f"'{self.sail}' -no_warn -c {sail_opts} {test.filename} -o {test.basename}"
            )
            step(
                f"gcc {test.basename}.c '{self.sail_dir}'/lib/*.c -lgmp -I '{self.sail_dir}'/lib -o {test.basename}"
            )
            step(f"./{test.basename}")
            step(f"rm {test.basename}.c")
            step(f"rm {test.basename}.h")
            step(f"rm {test.basename}")

        self.run_tests(name, Batcher(_SUITE_DIR), fn, testdir=_SUITE_DIR)


@suite("builtins.ocaml")
class BuiltinsOcamlTests(SailTest):
    def run(self):
        self.banner("Testing builtins: OCaml")
        self.run_tests("OCaml", Batcher(_SUITE_DIR), self._test, testdir=_SUITE_DIR)

    def _test(self, test):
        step(
            f"'{self.sail}' -no_warn -ocaml -ocaml_build_dir _sbuild_{test.basename} -o {test.basename} {test.filename}"
        )
        step(f"./{test.basename}")
        step(f"rm -r _sbuild_{test.basename}")
        step(f"rm {test.basename}")


@suite("builtins.lem")
class BuiltinsLemTests(SailTest):
    def run(self):
        self.banner("Testing builtins: Lem to OCaml")
        self.run_tests(
            "Lem to OCaml", Batcher(_SUITE_DIR), self._test, testdir=_SUITE_DIR
        )

    def _test(self, test):
        step(f"'{self.sail}' -no_warn -lem -o {test.basename} {test.filename}")
        step(f"mkdir -p _lbuild_{test.basename}")
        step(f"mv {test.basename}.lem _lbuild_{test.basename}")
        step(f"mv {test.basename}_types.lem _lbuild_{test.basename}")
        step(f"cp myocamlbuild.ml _lbuild_{test.basename}")
        step(f"cp '{self.sail_dir}'/src/gen_lib/*.lem _lbuild_{test.basename}")
        os.chdir(f"_lbuild_{test.basename}")
        step(f"ocamlbuild -package lem {test.basename}.native")
        step(f"./{test.basename}.native")
        os.chdir("..")
        step(f"rm -r _lbuild_{test.basename}")


@suite("builtins.coq")
class BuiltinsCoqTests(SailTest):
    def run(self):
        self.banner("Testing builtins: Coq")
        self.run_tests("Coq", Batcher(_SUITE_DIR), self._test, testdir=_SUITE_DIR)

    def _test(self, test):
        step(
            f"'{self.sail}' --no-warn --coq --coq-lib-style stdpp --coq-record-update"
            f" --undefined-gen -o {test.basename} {test.filename}"
        )
        step(f"mkdir -p _coqbuild_{test.basename}")
        step(f"mv {test.basename}.v _coqbuild_{test.basename}")
        step(f"mv {test.basename}_types.v _coqbuild_{test.basename}")
        step(f"cp test.v _coqbuild_{test.basename}")
        os.chdir(f"_coqbuild_{test.basename}")
        step(f"coqc {test.basename}_types.v")
        step(f"coqc {test.basename}.v")
        step(
            f"coqtop -require-import {test.basename}_types -require-import {test.basename}"
            f" -l test.v -batch | tee /dev/stderr | grep -q OK"
        )
        os.chdir("..")
        step(f"rm -r _coqbuild_{test.basename}")


@suite("builtins.isla")
class BuiltinsIslaTests(SailTest):
    def run(self):
        self.banner("Testing builtins: Isla")
        self.run_tests("Isla", Batcher(_SUITE_DIR), self._test, testdir=_SUITE_DIR)

    def _test(self, test):
        isla_dir = os.environ["ISLA_DIR"]
        step(
            f"'{isla_dir}'/isla-sail/isla-sail {test.filename}"
            f" '{self.sail_dir}'/lib/vector_dec.sail"
            f" '{isla_dir}'/test/property/include/config.sail -o {test.basename}"
        )
        step(
            f"'{isla_dir}'/target/release/isla-execute-function"
            f" -A {test.basename}.ir -C '{isla_dir}'/configs/plain.toml main"
        )
        step(f"rm {test.basename}.ir")
