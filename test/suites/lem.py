import os
import sys
from shutil import which


from sailtest import *

_TYPECHECK_PASS_DIR = os.path.join(TEST_DIR, "typecheck", "pass")

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


class _LemTests(SailTest):
    def _run_with_opts(self, name, opts, skip):
        if which("cvc4") is None:
            skip_tests.add("type_pow_zero")
            skip_tests_mwords.add("type_pow_zero")

        self.banner(f"Testing Lem with {name} (opts: '{opts}')")
        self.run_tests(
            name,
            Batcher(_TYPECHECK_PASS_DIR),
            self._make_test(opts),
            skip_set=skip,
        )

    def _make_test(self, opts):
        def fn(test):
            test.copy_filename()
            step(
                f"'{self.sail}' --lem{opts} --strict-bitvector -o {test.basename} {test.filename}"
            )
            step(
                f"lem -lib '{self.sail_dir}'/src/gen_lib {test.basename}_types.lem {test.basename}.lem"
            )

        return fn


@suite("lem.bitlists")
class LemBitlistsTests(_LemTests):
    def run(self):
        self._run_with_opts("bitlists", "", skip_tests)


@suite("lem.mwords")
class LemMachineWordsTests(_LemTests):
    def run(self):
        self._run_with_opts(
            "machine words", " --lem-mwords --auto-mono", skip_tests_mwords
        )
