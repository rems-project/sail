#!/usr/bin/env python3

import os
import sys
from shutil import which

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import *

test_dir = "../typecheck/pass"

skip_tests = {
    "phantom_option",
    "phantom_bitlist_union",
    # The Lem backend needs sail_mem_read to be instantiated at a minimum
    "concurrency_interface_dec",
    "concurrency_interface_inc",
    # Requires types that aren't currently in the library
    "float_prelude",
    # No possible configuration
    "config_mismatch",
    # Custom outcome
    "outcome_int",
    "outcome_impl_int",
}
skip_tests_mwords = {
    "phantom_option",
    "overload_plus",
    "vector_append_gen",
    "execute_decode_hard",
    "simple_record_access",
    "vector_append",
    "existential_constraint_synonym",
    "exist_tlb",
    "negative_bits_union",
    "while_MM",
    "while_PM",
    "zero_length_bv",
    "negative_bits_list",
    "patternrefinement",
    "abstract_extend",
    "issue984",
    # Due to an incompatibility between -auto_mono and -smt_linearize
    "pow_32_64",
    # The Lem backend needs sail_mem_read to be instantiated at a minimum
    "concurrency_interface_dec",
    "concurrency_interface_inc",
    "wf_register_type",
    "bitfield_exponential",
    "bitfield_abs",
    "bitfield_mod",
    "bitfield_empty",
    # Abstract types not implemented for Lem yet
    "abstract_bool",
    "abstract_bool2",
    "constraint_syn",
    "ex_vector_infer",
    "ex_list_infer",
    "ex_cons_infer",
    # Requires types that aren't currently in the library
    "float_prelude",
    # Needs smarter monomorphisation
    "bits_alias_cast",
    # No possible configuration
    "config_mismatch",
    # Custom outcome
    "outcome_int",
    "outcome_impl_int",
    # Type level if-then-else
    "if_unify",
}


class LemTests(SailTest):
    def run(self):
        if which("cvc4") is None:
            skip_tests.add("type_pow_zero")
            skip_tests_mwords.add("type_pow_zero")

        self.banner("Testing Lem with bitlists")
        self.run_tests(
            "with bitlists",
            os.listdir(test_dir),
            self._make_test(""),
            skip_set=skip_tests,
        )

        self.banner("Testing Lem with machine words")
        self.run_tests(
            "with machine words",
            os.listdir(test_dir),
            self._make_test("-lem_mwords -auto_mono"),
            skip_set=skip_tests_mwords,
        )

    def _make_test(self, opts):
        def fn(filename, basename):
            step(
                "'{}' --lem {} --strict-bitvector -o {} {}/{}".format(
                    self.sail, opts, basename, test_dir, filename
                )
            )
            step(
                "lem -lib '{}'/src/gen_lib {}_types.lem {}.lem".format(
                    self.sail_dir, basename, basename
                )
            )
            step("rm {}_types.lem {}.lem".format(basename, basename))

        return fn


LemTests().main()
