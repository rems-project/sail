#!/usr/bin/env python3

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from sailtest import *

_SUITE_DIR = os.path.dirname(os.path.abspath(__file__))
_EXEC_DIR = os.path.join(_SUITE_DIR, "..", "exec")

skip_selftests = {
    "outcome_impl",  # custom outcome types (not expected to work)
    "outcome_impl_int",  # custom outcome types (not expected to work)
    "outcome_impl_bool",  # custom outcome types (not expected to work)
    "union_variant_names",
    "varswap",
    "real",
    "poly_outcome",
    "string_of_bits",
    "pointer_assign",
    "concurrency_interface",
    "for_shadow",
    "string_literal_type",
    "issue429",
    "pc_no_wildcard",
    "type_if_bits",
    "nexp_simp_euclidian",
    "issue136",
    "anf_as_pattern",
    "real_prop",
    "constructor247",
    "deep_poly_nest",
    "config_abstract_bool",  # Register type unsupported in state.ml
    "newtype",
    "concurrency_interface_v2",
    "concurrency_interface_v2_var",
    "config_map_guard",
    "let_assert",
}


class LeanTests(SailTest):
    def run(self):
        self.banner("Cloning the support library")
        support_lib_lean = self._get_support_lib(_SUITE_DIR)
        print("...done!")
        self.banner("Testing lean target (sub-directory: lean)")
        self.run_tests(
            "lean",
            os.listdir(_SUITE_DIR),
            self._make_test(support_lib_lean, runnable=False),
            testdir=_SUITE_DIR,
        )

        self.banner("Cloning the support library")
        support_lib_exec = self._get_support_lib(_EXEC_DIR)
        print("...done!")
        self.banner("Testing lean target (sub-directory: exec)")
        self.run_tests(
            "c (lean runnable)",
            os.listdir(_EXEC_DIR),
            self._make_test(
                support_lib_exec, runnable=True, skip_list=skip_selftests
            ),
            testdir=_EXEC_DIR,
            skip_fn=self._make_skip_fn(skip_selftests),
        )

    def _get_support_lib(self, testdir):
        local = args.lean_local_support_library
        if local:
            return local
        lib_path = os.path.join(testdir, "support-lib")
        step(f"rm -rf '{lib_path}' || true")
        step(f"git clone https://github.com/rems-project/lean-sail.git '{lib_path}'")
        print("Building the support library")
        step("lake build", cwd=lib_path)
        return "../../support-lib"

    def _make_skip_fn(self, skip_list):
        def skip_fn(filename, basename):
            return not args.run_skips and basename in skip_list

        return skip_fn

    def _make_test(self, support_lib, runnable, skip_list=None):
        def fn(filename, basename):
            is_skip = skip_list is not None and basename in skip_list and args.run_skips
            # The forked child's cwd is already set to testdir by run_tests().
            step(f"rm -rf {basename} || true")
            step(f"mkdir -p {basename}")
            extra_flags = (
                ["--splice", "coq-print.splice", "--strict-bitvector"]
                if runnable
                else ["--lean-matchbv"]
            )
            extra_flags_str = " ".join(extra_flags)
            step(
                f"'{self.sail}' {extra_flags_str} {filename} --lean --lean-single-file"
                f" --lean-executable --lean-output-dir {basename} --lean-lib-path {support_lib}",
                name=filename,
            )
            step(f"lake update", cwd=f"{basename}/out", name=filename)
            if runnable:
                expected_status = 1 if basename.startswith("fail") else 0
                step(
                    "lake exe run > expected 2> err_status",
                    cwd=f"{basename}/out",
                    name=filename,
                    expected_status=expected_status,
                    stderr_file=f"{basename}/out/err_status",
                )
            else:
                step(f"lake update", cwd=f"{basename}/out", name=filename)
                step(f"lake build", cwd=f"{basename}/out", name=filename)

            if not runnable:
                output = f"{basename}/output"
                step(f"cat {basename}/out/Out/Defs.lean > {output}")
                step(
                    f'echo >> {output}; echo "XXXXXXXXX" >> {output}; echo >> {output}'
                )
                step(f"cat {basename}/out/Out.lean >> {output}")
                status = step_with_status(
                    f"diff {output} {basename}.expected.lean", name=filename
                )
                if status != 0:
                    if args.update_expected:
                        print(f"Overriding file {basename}.expected.lean")
                        step(f"cp {output} {basename}.expected.lean")
                    else:
                        sys.exit(1)
            else:
                status = step_with_status(
                    f"diff {basename}/out/expected {basename}.expect", name=filename
                )
                if status != 0:
                    sys.exit(1)

            step(f"rm -rf {basename}")
            if is_skip:
                print(f"{basename} now passes!")

        return fn


LeanTests().main(xml_dir=_SUITE_DIR)
