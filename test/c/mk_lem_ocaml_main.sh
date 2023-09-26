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
