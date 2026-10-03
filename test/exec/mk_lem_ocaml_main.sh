#!/bin/bash

if grep -q 'val main : unit -> unit' "$1.lem"; then
  echo "$2.main ();;" > main.ml
  LIBRARIES="prompt prompt_monad undefined"
  if grep -q 'Sail2_operators_mwords' "$1.lem"; then
    LIBRARIES="$LIBRARIES operators_mwords"
  fi
else
  if grep -q 'initial_regstate' "$1.lem"; then
    REGSTATE="$2.initial_regstate"
  else
    REGSTATE='()'
  fi
  if grep -q 'Sail2_concurrency_interface_v2' "$1.lem"; then
    TEMPLATE=lem-ocaml-template-v2.ml
    LIBRARIES="concurrency_interface_v2 concurrency_interface_mwords_v2 concurrency_interface_bitlists_v2 monadic_combinators_v2 undefined_concurrency_interface_v2"
    mv undefined_override.lem_v2 undefined_override.lem
  else
    TEMPLATE=lem-ocaml-template.ml
    LIBRARIES="prompt prompt_monad undefined"
  fi
  if grep -q 'Sail2_operators_mwords' "$1.lem"; then
    LIBRARIES="$LIBRARIES operators_mwords"
    FROMADDR='Z.to_int (Lem.naturalFromWord bs)'
  else
    FROMADDR='match unsigned_of_bits bs with Some i -> Z.to_int i | None -> failwith "Bad address"'
  fi
  sed -e "s/MODULENAME/$2/g" -e "s/REGSTATE/$REGSTATE/g" -e "s/FROMADDR/$FROMADDR/g" < ../$TEMPLATE > main.ml
fi

# Copy only the library files we need
for f in "instr_kinds" "operators_bitlists" "operators" "state" "state_monad" "string" "values" $LIBRARIES; do
  cp "$3/src/gen_lib/sail2_$f.lem" .
done
