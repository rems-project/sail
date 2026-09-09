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

if grep -q 'Sail2_concurrency_interface_v2' "_holbuild_${BASENAME}/${BASENAME}.lem"; then
  cp lbuild/undefined_override.lem_v2 "_holbuild_${BASENAME}/undefined_override.lem" <<EOF
EOF
elif grep -q 'Sail2_concurrency_interface' "_holbuild_${BASENAME}/${BASENAME}.lem"; then
  cp lbuild/undefined_override.lem_v1 "_holbuild_${BASENAME}/undefined_override.lem" <<EOF
EOF
else
  sed -e "s/Bitvector 'a, Register_Value 'rv/Bitvector 'a/" \
      -e "s/Register_Value .rv => //" \
      lbuild/undefined_override.lem > _holbuild_${BASENAME}/undefined_override.lem
fi
