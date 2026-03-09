import os
import sys
import shutil


from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "exec")

def _no_valgrind():
    try:
        subprocess.call(["valgrind", "--version"])
        return False
    except FileNotFoundError:
        return True

class _ExecBase(SailTest):
    """Shared helper for all exec sub-suites. Not registered."""

    def prepare(self):
        includes = os.path.join(_SUITE_DIR, "includes")
        work_includes = os.path.join(self.work_dir, "includes")
        if os.path.exists(includes) and not os.path.exists(work_includes):
            shutil.copytree(includes, work_includes)

class _ExecCBase(_ExecBase):
    """Shared helper for the C and C++ exec sub-suites. Not registered."""

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

        def fn(test):
            test.copy_filename()
            step(
                f"'{self.sail}' --no-warn {target_opt} {sail_opts} {test.filename} -o {test.basename}"
            )
            step(
                f"{compiler} {c_opts} {test.basename}.{extension}"
                f" '{self.sail_dir}'/lib/*.c -lgmp -I '{self.sail_dir}'/lib -o {test.basename}.bin"
            )
            step(
                f"./{test.basename}.bin > {test.basename}.result 2> {test.basename}.err_result",
                expected_status=1 if test.basename.startswith("fail") else 0,
                stderr_file=f"{test.basename}.err_result",
            )
            step(f"diff {test.basename}.result {test.expect}")
            if os.path.exists(test.err_expect):
                step(f"diff {test.basename}.err_result {test.err_expect}")
            if valgrind and not test.basename.startswith("fail"):
                step(
                    f"valgrind --leak-check=full --track-origins=yes"
                    f" --errors-for-leak-kinds=all --error-exitcode=2 ./{test.basename}.bin",
                    expected_status=1 if test.basename.startswith("fail") else 0,
                )

        self.run_tests(
            name,
            Batcher(_SUITE_DIR),
            fn,
            expected_failures=expected_failures,
        )

@suite("exec.c.unopt.default")
class ExecCUnoptTests(_ExecCBase):
    def run(self):
        self._run_c_tests("unoptimized C", "", "", False)

@suite("exec.c.unopt.nomangle")
class ExecCUnoptTests(_ExecCBase):
    def run(self):
        self._run_c_tests("unoptimized C", "", "--c-no-mangle", False)

@suite("exec.c.constant_fold")
class ExecCConstantFoldTests(_ExecCBase):
    def run(self):
        self._run_c_tests("constant folding", "", "-Oconstant_fold", False)

@suite("exec.c.opt.default")
class ExecCOptTests(_ExecCBase):
    def run(self):
        self._run_c_tests("optimized C", "-O2", "-O", False)

@suite("exec.c.opt.valgrind")
class ExecCOptValgrindTests(_ExecCBase):
    def run(self):
        self._run_c_tests("optimized C", "-O2", "-O", True)

@suite("exec.c.opt.ubsan")
class ExecCUBSanTests(_ExecCBase):
    def run(self):
        self._run_c_tests(
            "undefined behavior sanitised", "-O2 -fsanitize=undefined", "-O", False
        )

@suite("exec.c.opt.asan")
class ExecCASanTests(_ExecCBase):
    def run(self):
        self._run_c_tests(
            "address sanitised", "-O2 -fsanitize=address -g", "-O", False
        )

_cpp_xfails = {
    "cabbrev.sail": "my_pair_in_c is declared in a namespace in C++",
    "xlen_val.sail": "assumes variables are still global",
    # TODO: These use `$c_in_main` to add a call to `sail_set_abstract_xlen(32)` to `main()`
    # but for C++ it needs to go in `model_main()` and be `model.sail_set_abstract_xlen(32)`.
    "abstract_sizeof_no_use.sail": "difficult to call model.sail_set_abstract_... in the right place",
    "abstract_type.sail": "difficult to call model.sail_set_abstract_... in the right place",
    "tl_let_flow_change.sail": "difficult to call model.sail_set_abstract_... in the right place",
}

@suite("exec.c.with_cpp.unopt")
class ExecCCppUnoptTests(_ExecCBase):
    def run(self):
        self._run_c_tests(
            "unoptimized C with C++ compiler", "-xc++", "", False, compiler="c++"
        )

@suite("exec.c.with_cpp.opt")
class ExecCCppOptTests(_ExecCBase):
    def run(self):
        self._run_c_tests(
            "optimized C with C++ compiler", "-xc++ -O2", "-O", False, compiler="c++"
        )

@suite("exec.c.with_cpp.valgrind")
class ExecCCppOptValgrindTests(_ExecCBase):
    def run(self):
        self._run_c_tests(
            "optimized C with C++ compiler", "-xc++ -O2", "-O", True, compiler="c++"
        )

@suite("exec.cpp.unopt")
class ExecCppUnoptTests(_ExecCBase):
    def run(self):
        self._run_c_tests(
            "unoptimized C++",
            "",
            "",
            False,
            compiler="c++",
            actually_cpp=True,
            expected_failures=_cpp_xfails,
        )

@suite("exec.cpp.opt")
class ExecCppOptTests(_ExecCBase):
    def run(self):
        self._run_c_tests(
            "optimized C++",
            "-O2",
            "-O",
            True,
            compiler="c++",
            actually_cpp=True,
            expected_failures=_cpp_xfails,
        )


@suite("exec.interpreter")
class ExecInterpreterTests(_ExecBase):
    def prepare(self):
        super(ExecInterpreterTests, self).prepare(_SUITE_DIR)
        commands = os.path.join(_SUITE_DIR, "execute.isail")
        work_commands = os.path.join(self.work_dir, "execute.isail")
        shutil.copy(commands, work_commands)

    def run(self):
        if os.name == "posix":
            self.banner("Testing interpreter")
            self.run_tests(
                "interpreter",
                Batcher(_SUITE_DIR),
                self._test,
            )
        else:
            print(
                "Skipping interpreter tests because the interpreter is only supported on Unix-like platforms"
            )

    def _test(self, test):
        test.copy_filename()
        step(
            f"timeout 10s '{self.sail}' -undefined_gen -is execute.isail"
            f" -iout {test.basename}.iresult {test.filename}"
        )
        step(f"diff {test.basename}.iresult {test.expect}")


@suite("exec.ocaml")
class ExecOcamlTests(_ExecBase):
    def run(self):
        self.banner("Testing OCaml")
        self.run_tests(
            "OCaml", Batcher(_SUITE_DIR), self._test
        )

    def _test(self, test):
        test.copy_filename()
        step(
            f"'{self.sail}' --ocaml --ocaml-build-dir _sbuild_{test.basename} -o {test.basename}_ocaml {test.filename}"
        )
        step(
            f"dune exec --release {test.basename}_ocaml 1> ../{test.basename}.oresult",
            expected_status=1 if test.basename.startswith("fail") else 0,
            cwd=f"_sbuild_{test.basename}",
        )
        step(f"diff {test.basename}.oresult {test.expect}")


@suite("exec.lem")
class ExecLemTests(_ExecBase):
    def prepare(self):
        super(ExecLemTests, self).prepare(_SUITE_DIR)
        commands = os.path.join(_SUITE_DIR, "mk_lem_ocaml_main.sh")
        work_commands = os.path.join(self.work_dir, "mk_lem_ocaml_main.sh")
        shutil.copy(commands, work_commands)
        commands = os.path.join(_SUITE_DIR, "lem-ocaml-template.ml")
        work_commands = os.path.join(self.work_dir, "lem-ocaml-template.ml")
        shutil.copy(commands, work_commands)

    def run(self):
        self.banner("Testing lem")
        self.run_tests(
            "lem",
            Batcher(_SUITE_DIR),
            self._test,
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

    def _test(self, test):
        test.copy_filename()
        step(f"'{self.sail}' -lem -lem_lib Undefined_override -o {test.basename} {test.filename}")
        step(f"mkdir -p _lbuild_{test.basename}")
        step(f"mv {test.basename}.lem {test.basename}_types.lem _lbuild_{test.basename}")
        step(f"rm {test.basename.capitalize()}_lemmas.thy")
        step(f"cp {test.directory}/lbuild/* _lbuild_{test.basename}")
        os.chdir(f"_lbuild_{test.basename}")
        step(
            f"../mk_lem_ocaml_main.sh {test.basename} {test.basename.capitalize()} {self.sail_dir}"
        )
        step("lem -lib .. -ocaml *.lem")
        step("ocamlbuild -use-ocamlfind main.native")
        step(
            f"./main.native 1> {test.basename}.lresult 2> {test.basename}.lerr",
            expected_status=1 if test.basename.startswith("fail") else 0,
        )
        step(f"diff {test.expect} {test.basename}.lresult")
        if os.path.exists(test.err_expect):
            step(f"diff {test.basename}.lerr {test.err_expect}")
        os.chdir("..")


@suite("exec.coq")
class ExecCoqTests(_ExecBase):
    def run(self):
        self.banner("Testing coq")
        self.run_tests(
            "coq",
            Batcher(_SUITE_DIR),
            self._test,
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

    def _test(self, test):
        step(
            f"'{self.sail}' -coq -coq-record-update -D PRINT_EFFECTS"
            f" -splice coq-print.splice -undefined_gen -o {test.basename} {test.filename}"
        )
        step(f"mkdir -p _coqbuild_{test.basename}")
        step(f"mv {test.basename}.v _coqbuild_{test.basename}")
        step(f"mv {test.basename}_types.v _coqbuild_{test.basename}")
        step(f"./mk_coq_main.sh {test.basename} {test.basename.capitalize()}")
        os.chdir(f"_coqbuild_{test.basename}")
        step(f"coqc {test.basename}_types.v")
        step(f"coqc {test.basename}.v")
        step(
            f"coqtop -require-import {test.basename}_types -require-import {test.basename}"
            f" -l main.v -batch | tee /dev/stderr | grep -q OK",
            expected_status=1 if test.basename.startswith("fail") else 0,
        )
        filter_command = "ocaml ../coq_output_filter.ml < "
        step(f"{filter_command} output.out | diff - ../{test.basename}.expect")
        if os.path.exists(f"../{test.basename}.err_expect"):
            step(f"{filter_command} error.out | diff - ../{test.basename}.err_expect")
        os.chdir("..")
        step(f"rm -r _coqbuild_{test.basename}")
