#!/bin/bash

if grep -q 'val main : unit -> unit' "$1.lem"; then
  echo "$2.main ();;" > main.ml
else
  if grep -q 'initial_regstate' "$1.lem"; then
    REGSTATE="$2.initial_regstate"
  else
    REGSTATE='()'
  fi
  sed -e "s/MODULENAME/$2/g" -e "s/REGSTATE/$REGSTATE/g" < ../lem-ocaml-template.ml > main.ml
fi

# Copy only the library files we need
for f in "instr_kinds" "operators_bitlists" "operators" "prompt" "prompt_monad" "state" "state_monad" "string" "undefined" "values"; do
  cp "$3/src/gen_lib/sail2_$f.lem" .
done
