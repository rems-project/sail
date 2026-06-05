#!/bin/bash

BASENAME="$1"
SAIL_DIR="$2"

cat > "_holbuild_${BASENAME}/main.sml" <<EOF
load "${BASENAME}Theory";
open Lib Term Type boolSyntax;

(* Compute with definitions even when we have not proved their termination *)
let val missing_defs = computeLib.unmapped (!computeLib.the_compset) |> List.filter (fn (_,thy) => String.isPrefix "sail2_" thy orelse thy = "${BASENAME}")
    val add = List.map (fn (name,thy) => DB.fetch thy (name ^ "_def")) missing_defs
in computeLib.add_funs add
end

fun is_monadic t = (type_of t |> strip_fun |> fst |> length) > 2

val (term, check) =
  if is_monadic \`\`main\`\` then
    let val tm = if is_monadic \`\`sail_model_init\`\` then \`\`seqS (sail_model_init ()) (main ()) ARB\`\` else \`\`main () ARB\`\`
        fun check result =
          pred_setSyntax.strip_set result |>
          List.all (fn r => r |>
            pairSyntax.dest_pair |> fst |>
            strip_comb |> fst |>
            dest_const |> fst |>
            fn s => s = "Value")
    in (tm, check)
    end
   else (\`\`main ()\`\`, is_const);
val result = rhs (Thm.concl (bossLib.EVAL term));
OS.Process.exit (if check result then OS.Process.success else OS.Process.failure) : unit
EOF

cat > "_holbuild_${BASENAME}/Holmakefile" <<EOF
INCLUDES = \$(LEM_DIR)/hol-lib ${SAIL_DIR}/lib/hol
EOF

if grep -q 'Sail2_concurrency_interface' "_holbuild_${BASENAME}/${BASENAME}.lem"; then
  cat > "_holbuild_${BASENAME}/undefined_override.lem" <<EOF
open import Pervasives_extra
open import Sail2_values
open import Sail2_concurrency_interface

(* Override the normal definitions for these to provide something
   executable and determinstic.

   The Lem files are compiled individually here, so we need to include
   the modules with the definitions that we're overriding to ensure a
   consistent renaming by Lem. *)

open import Sail2_undefined

val internal_pick : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'a 'e. list 'a -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'a 'e
let internal_pick l =
  match l with
  | [] -> Fail "internal_pick on empty list"
  | h :: _ -> return h
  end

val undefined_bitvector : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'a 'e. Bitvector 'a => integer -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'a 'e
let undefined_bitvector n = return (of_int n 0)

let undefined_bits = undefined_bitvector
val undefined_bit : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'e. unit -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval bitU 'e
let undefined_bit () = return BU
val undefined_bool : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'e. unit -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval bool 'e
let undefined_bool () = return false
val undefined_string : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'e. unit -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval string 'e
let undefined_string () = return "undefined_string"
val undefined_int : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'e. unit -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval integer 'e
let undefined_int () = return (0 : integer)
val undefined_nat : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'e. unit -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval integer 'e
let undefined_nat () = return (0 : integer)
val undefined_real : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'e. unit -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval real 'e
let undefined_real () = return (0 : real)
val undefined_range : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'e. integer -> integer -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval integer 'e
let undefined_range i j = return i
val undefined_atom : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'e. integer -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval integer 'e
let undefined_atom i = return i

val undefined_list : forall 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval 'a 'e. 'a -> monad 'abort 'barrier 'cache_op 'fault 'pa 'tlb_op 'translation_summary 'trans_start 'trans_end 'arch_ak 'regval (list 'a) 'e
let undefined_list a = return []

EOF
else
  sed -e "s/Bitvector 'a, Register_Value 'rv/Bitvector 'a/" \
      -e "s/Register_Value .rv => //" \
      lbuild/undefined_override.lem > _holbuild_${BASENAME}/undefined_override.lem
fi
