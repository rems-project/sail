import os
import sys


from sailtest import *

_TEST_DIR = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
)
_SUITE_DIR = os.path.join(_TEST_DIR, "exec")

_cpp_xfails = {
    "cabbrev.sail": "my_pair_in_c is declared in a namespace in C++",
    "xlen_val.sail": "assumes variables are still global",
    # TODO: These use `$c_in_main` to add a call to `sail_set_abstract_xlen(32)` to `main()`
    # but for C++ it needs to go in `model_main()` and be `model.sail_set_abstract_xlen(32)`.
    "abstract_sizeof_no_use.sail": "difficult to call model.sail_set_abstract_... in the right place",
    "abstract_type.sail": "difficult to call model.sail_set_abstract_... in the right place",
    "tl_let_flow_change.sail": "difficult to call model.sail_set_abstract_... in the right place",
}


def _no_valgrind():
    try:
        subprocess.call(["valgrind", "--version"])
        return False
    except FileNotFoundError:
        return True


class ExecTests(SailTest):
    def run(self):
        targets = self.get_targets(["c", "cpp", "interpreter", "ocaml"])
        print(f"Targets: {targets}")

        if "c" in targets:
            self._run_c_tests("unoptimized C", "", "--c-no-mangle", False)
            self._run_c_tests("unoptimized C", "", "", False)
            self._run_c_tests("optimized C", "-O2", "-O", True)
            self._run_c_tests("constant folding", "", "-Oconstant_fold", False)
            self._run_c_tests(
                "undefined behavior sanitised", "-O2 -fsanitize=undefined", "-O", False
            )
            self._run_c_tests(
                "address sanitised", "-O2 -fsanitize=address -g", "-O", False
            )

        if "cpp" in targets:
            # Compiling the C as if it was C++.
            self._run_c_tests(
                "unoptimized C with C++ compiler", "-xc++", "", False, compiler="c++"
            )
            self._run_c_tests(
                "optimized C with C++ compiler", "-xc++ -O2", "-O", True, compiler="c++"
            )

            # Actual C++ output.
            self._run_c_tests(
                "unoptimized C++",
                "",
                "",
                False,
                compiler="c++",
                actually_cpp=True,
                expected_failures=_cpp_xfails,
            )
            self._run_c_tests(
                "optimized C++",
                "-O2",
                "-O",
                True,
                compiler="c++",
                actually_cpp=True,
                expected_failures=_cpp_xfails,
            )

        if "interpreter" in targets:
            if os.name == "posix":
                self.banner("Testing interpreter")
                self.run_tests(
                    "interpreter",
                    Batcher(_SUITE_DIR),
                    self._test_interpreter,
                    testdir=_SUITE_DIR,
                )
            else:
                print(
                    "Skipping interpreter tests because the interpreter is only supported on Unix-like platforms"
                )

        if "ocaml" in targets:
            self.banner("Testing OCaml")
            self.run_tests(
                "OCaml", Batcher(_SUITE_DIR), self._test_ocaml, testdir=_SUITE_DIR
            )

        if "lem" in targets:
            self.banner("Testing lem")
            self.run_tests(
                "lem",
                Batcher(_SUITE_DIR),
                self._test_lem,
                testdir=_SUITE_DIR,
                expected_failures={
                    "inc_tests.sail": "missing built-in functions for increasing vectors in Lem library",
                    "read_write_ram.sail": "uses memory primitives not provided by default in Lem",
                    "fail_exception.sail": "try-blocks around pure expressions not supported in Lem (and a little silly)",
                    "loop_exception.sail": "try-blocks around pure expressions not supported in Lem (and a little silly)",
                    "real.sail": "print_real not available for Lem at present",
                    "real_prop.sail": "print_real not available for Lem at present",
                    "concurrency_interface.sail": "test doesn't meet Lem library's expectations for the concurrency interface",
                    "concurrency_interface_v2.sail": "test doesn't meet Lem library's expectations for the concurrency interface",
                    "concurrency_interface_write.sail": "test harness doesn't meet Lem library's expectations for the concurrency interface",
                    "pc_no_wildcard.sail": "register type unsupported by Lem backend",
                    "cheri_capreg.sail": "test has strange 'pure' reg_deref",
                    "constructor247.sail": "don't attempt to support so many constructors in lem -> ocaml builds",
                    "either.sail": "Lem breaks because it has the same name as a library module",
                    "poly_outcome.sail": "test doesn't meet Lem library's expectations for the concurrency interface",
                    "config_abstract_bool.sail": "type-level if not yet supported",
                    "outcome_impl_int.sail": "unsupported outcome",
                    "outcome_impl_bool.sail": "unsupported outcome",
                },
            )

        if "coq" in targets:
            self.banner("Testing coq")
            self.run_tests(
                "coq",
                Batcher(_SUITE_DIR),
                self._test_coq,
                testdir=_SUITE_DIR,
                expected_failures={
                    "inc_tests.sail": "missing built-in functions for increasing vectors in Coq library",
                    "read_write_ram.sail": "uses memory primitives not provided by default in Coq",
                    "fail_exception.sail": "test harness can't produce expected output for uncaught exception",
                    "loop_exception.sail": "Loop requiring termination measure with a register read",
                    "outcome_impl.sail": "test doesn't meet Coq backend's expectations for the concurrency interface",
                    "outcome_impl_int.sail": "test doesn't meet Coq backend's expectations for the concurrency interface",
                    "outcome_impl_bool.sail": "test doesn't meet Coq backend's expectations for the concurrency interface",
                    "pc_no_wildcard.sail": "register type unsupported by Coq backend",
                    "poly_outcome.sail": "test doesn't meet Coq library's expectations for the concurrency interface",
                    "poly_mapping.sail": "test requires non-standard hex built-ins",
                    "real.sail": "print_real not available for Coq at present",
                    "real_prop.sail": "random_real not available for Coq at present",
                    "for_shadow.sail": "bug: remove_e_assign rewrite assumes <= available",
                    "newtype.sail": "Type definition with a parameter that should be merged, inferred, or made explicit",
                    "simple_while.sail": "Loop without termination measure",
                    "simple_while2.sail": "Loop without termination measure",
                    "simple_while3.sail": "Loop without termination measure",
                },
            )

    def _run_c_tests(
        self,
        name,
        c_opts,
        sail_opts,
        valgrind,
        compiler="cc",
        actually_cpp=False,
        expected_failures=None,
    ):
        """Run a C/C++ test suite, handling the valgrind-unavailable case."""
        self.banner(
            f"Testing {name} with C options: {c_opts} Sail options: {sail_opts} valgrind: {valgrind}"
        )
        if valgrind and _no_valgrind():
            print("skipping because no valgrind found")
            self._xml_parts.append(Results(name).finish())
            return
        extension = "cpp" if actually_cpp else "c"
        target_opt = "--cpp" if actually_cpp else "-c"

        def fn(filename, basename):
            step(
                f"'{self.sail}' --no-warn {target_opt} {sail_opts} {filename} -o {basename}"
            )
            step(
                f"{compiler} {c_opts} {basename}.{extension}"
                f" '{self.sail_dir}'/lib/*.c -lgmp -I '{self.sail_dir}'/lib -o {basename}.bin"
            )
            step(
                f"./{basename}.bin > {basename}.result 2> {basename}.err_result",
                expected_status=1 if basename.startswith("fail") else 0,
                stderr_file=f"{basename}.err_result",
            )
            step(f"diff {basename}.result {basename}.expect")
            if os.path.exists(f"{basename}.err_expect"):
                step(f"diff {basename}.err_result {basename}.err_expect")
            if valgrind and not basename.startswith("fail"):
                step(
                    f"valgrind --leak-check=full --track-origins=yes"
                    f" --errors-for-leak-kinds=all --error-exitcode=2 ./{basename}.bin",
                    expected_status=1 if basename.startswith("fail") else 0,
                )
            step(
                f"rm {basename}.{extension} {basename}.h {basename}.bin {basename}.result"
            )

        self.run_tests(
            name,
            Batcher(_SUITE_DIR),
            fn,
            testdir=_SUITE_DIR,
            expected_failures=expected_failures,
        )

    def _test_interpreter(self, filename, basename):
        step(
            f"timeout 10s '{self.sail}' -undefined_gen -is execute.isail"
            f" -iout {basename}.iresult {filename}"
        )
        step(f"diff {basename}.iresult {basename}.expect")
        step(f"rm {basename}.iresult")

    def _test_ocaml(self, filename, basename):
        step(
            f"'{self.sail}' --ocaml --ocaml-build-dir _sbuild_{basename} -o {basename}_ocaml {filename}"
        )
        step(
            f"dune exec --release {basename}_ocaml 1> ../{basename}.oresult",
            expected_status=1 if basename.startswith("fail") else 0,
            cwd=f"_sbuild_{basename}",
        )
        step(f"diff {basename}.oresult {basename}.expect")
        step(f"rm -rf _sbuild_{basename}")
        step(f"rm {basename}.oresult")

    def _test_lem(self, filename, basename):
        step(f"'{self.sail}' -lem -lem_lib Undefined_override -o {basename} {filename}")
        step(f"mkdir -p _lbuild_{basename}")
        step(f"mv {basename}.lem {basename}_types.lem _lbuild_{basename}")
        step(f"rm {basename.capitalize()}_lemmas.thy")
        step(f"cp lbuild/* _lbuild_{basename}")
        os.chdir(f"_lbuild_{basename}")
        step(
            f"../mk_lem_ocaml_main.sh {basename} {basename.capitalize()} {self.sail_dir}"
        )
        step("lem -lib .. -ocaml *.lem")
        step("ocamlbuild -use-ocamlfind main.native")
        step(
            f"./main.native 1> {basename}.lresult 2> {basename}.lerr",
            expected_status=1 if basename.startswith("fail") else 0,
        )
        step(f"diff ../{basename}.expect {basename}.lresult")
        if os.path.exists(f"../{basename}.err_expect"):
            step(f"diff {basename}.lerr ../{basename}.err_expect")
        os.chdir("..")
        step(f"rm -r _lbuild_{basename}")

    def _test_coq(self, filename, basename):
        step(
            f"'{self.sail}' -coq -coq-record-update -D PRINT_EFFECTS"
            f" -splice coq-print.splice -undefined_gen -o {basename} {filename}"
        )
        step(f"mkdir -p _coqbuild_{basename}")
        step(f"mv {basename}.v _coqbuild_{basename}")
        step(f"mv {basename}_types.v _coqbuild_{basename}")
        step(f"./mk_coq_main.sh {basename} {basename.capitalize()}")
        os.chdir(f"_coqbuild_{basename}")
        step(f"coqc {basename}_types.v")
        step(f"coqc {basename}.v")
        step(
            f"coqtop -require-import {basename}_types -require-import {basename}"
            f" -l main.v -batch | tee /dev/stderr | grep -q OK",
            expected_status=1 if basename.startswith("fail") else 0,
        )
        filter_command = "ocaml ../coq_output_filter.ml < "
        step(f"{filter_command} output.out | diff - ../{basename}.expect")
        if os.path.exists(f"../{basename}.err_expect"):
            step(f"{filter_command} error.out | diff - ../{basename}.err_expect")
        os.chdir("..")
        step(f"rm -r _coqbuild_{basename}")
