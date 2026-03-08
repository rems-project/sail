import os
import sys


from sailtest import *

_TEST_DIR = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
)
_SUITE_DIR = os.path.join(_TEST_DIR, "builtins")


class BuiltinsTests(SailTest):
    def run(self):
        targets = self.get_targets(["c", "ocaml"])
        print(f"Targets: {targets}")

        if "c" in targets:
            for name, sail_opts in [
                ("No optimisations", ""),
                ("Optimisations", "-O"),
                ("Constant folding", "-Oconstant_fold"),
            ]:
                self.banner(f"Testing builtins: C, {name} Sail options: {sail_opts}")
                self.run_tests(
                    f"C, {name}",
                    Batcher(_SUITE_DIR),
                    self._make_c_test(sail_opts),
                    testdir=_SUITE_DIR,
                )

        if "ocaml" in targets:
            self.banner("Testing builtins: OCaml")
            self.run_tests(
                "OCaml", Batcher(_SUITE_DIR), self._test_ocaml, testdir=_SUITE_DIR
            )

        if "lem" in targets:
            self.banner("Testing builtins: Lem to OCaml")
            self.run_tests(
                "Lem to OCaml", Batcher(_SUITE_DIR), self._test_lem, testdir=_SUITE_DIR
            )

        if "coq" in targets:
            self.banner("Testing builtins: Coq")
            self.run_tests(
                "Coq", Batcher(_SUITE_DIR), self._test_coq, testdir=_SUITE_DIR
            )

        if "isla" in targets:
            self.banner("Testing builtins: Isla")
            self.run_tests(
                "Isla", Batcher(_SUITE_DIR), self._test_isla, testdir=_SUITE_DIR
            )

    def _make_c_test(self, sail_opts):
        def fn(filename, basename):
            step(f"'{self.sail}' -no_warn -c {sail_opts} {filename} -o {basename}")
            step(
                f"gcc {basename}.c '{self.sail_dir}'/lib/*.c -lgmp -I '{self.sail_dir}'/lib -o {basename}"
            )
            step(f"./{basename}")
            step(f"rm {basename}.c")
            step(f"rm {basename}.h")
            step(f"rm {basename}")

        return fn

    def _test_ocaml(self, filename, basename):
        step(
            f"'{self.sail}' -no_warn -ocaml -ocaml_build_dir _sbuild_{basename} -o {basename} {filename}"
        )
        step(f"./{basename}")
        step(f"rm -r _sbuild_{basename}")
        step(f"rm {basename}")

    def _test_lem(self, filename, basename):
        step(f"'{self.sail}' -no_warn -lem -o {basename} {filename}")
        step(f"mkdir -p _lbuild_{basename}")
        step(f"mv {basename}.lem _lbuild_{basename}")
        step(f"mv {basename}_types.lem _lbuild_{basename}")
        step(f"cp myocamlbuild.ml _lbuild_{basename}")
        step(f"cp '{self.sail_dir}'/src/gen_lib/*.lem _lbuild_{basename}")
        os.chdir(f"_lbuild_{basename}")
        step(f"ocamlbuild -package lem {basename}.native")
        step(f"./{basename}.native")
        os.chdir("..")
        step(f"rm -r _lbuild_{basename}")

    def _test_coq(self, filename, basename):
        step(
            f"'{self.sail}' --no-warn --coq --coq-lib-style stdpp --coq-record-update"
            f" --undefined-gen -o {basename} {filename}"
        )
        step(f"mkdir -p _coqbuild_{basename}")
        step(f"mv {basename}.v _coqbuild_{basename}")
        step(f"mv {basename}_types.v _coqbuild_{basename}")
        step(f"cp test.v _coqbuild_{basename}")
        os.chdir(f"_coqbuild_{basename}")
        step(f"coqc {basename}_types.v")
        step(f"coqc {basename}.v")
        step(
            f"coqtop -require-import {basename}_types -require-import {basename}"
            f" -l test.v -batch | tee /dev/stderr | grep -q OK"
        )
        os.chdir("..")
        step(f"rm -r _coqbuild_{basename}")

    def _test_isla(self, filename, basename):
        isla_dir = os.environ["ISLA_DIR"]
        step(
            f"'{isla_dir}'/isla-sail/isla-sail {filename}"
            f" '{self.sail_dir}'/lib/vector_dec.sail"
            f" '{isla_dir}'/test/property/include/config.sail -o {basename}"
        )
        step(
            f"'{isla_dir}'/target/release/isla-execute-function"
            f" -A {basename}.ir -C '{isla_dir}'/configs/plain.toml main"
        )
        step(f"rm {basename}.ir")
