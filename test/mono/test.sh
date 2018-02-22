#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."
LEMDIR="$DIR/../../../lem"
OUTDIR="$DIR/test-out"
ZARITH="$LEMDIR/ocaml-lib/dependencies/zarith"

if [ ! -d "$OUTDIR" ]; then
  mkdir -- "$OUTDIR"
fi
cd "$OUTDIR"

TESTONLY="$1"
if [ -n "$TESTONLY" ]; then shift; fi

LOG="$DIR/log"
date > "$LOG"

exec 3< "$DIR/tests"
set +e

while read -u 3 TEST ARGS; do
  if [ -z "$TESTONLY" -o "$TEST" = "$TESTONLY" ]; then
  
    echo "$TEST lem - ocaml" | tee -a -- "$LOG"
    rm -f -- "$OUTDIR"/*
    "$SAILDIR/sail" -lem -lem_mwords "$DIR/$TEST".sail -o "$OUTDIR/testout" $ARGS $@ &>> "$LOG" && \
    "$LEMDIR/bin/lem" -ocaml -lib "$SAILDIR/src/lem_interp" "$SAILDIR/src/gen_lib/sail_values.lem" "$SAILDIR/src/gen_lib/sail_operators.lem" "$SAILDIR/src/gen_lib/sail_operators_mwords.lem" "$SAILDIR/src/lem_interp/sail_instr_kinds.lem" "$SAILDIR/src/gen_lib/prompt.lem" "$SAILDIR/src/gen_lib/state_monad.lem" "$SAILDIR/src/gen_lib/state.lem" "$SAILDIR/src/gen_lib/prompt_monad.lem" testout_types.lem testout.lem -outdir "$OUTDIR" &>> "$LOG" && \
    cp -- "$DIR"/test.ml "$OUTDIR" && \
    ocamlfind ocamlc -linkpkg -package zarith -package lem sail_values.ml sail_operators.ml sail_operators_mwords.ml sail_instr_kinds.ml prompt_monad.ml prompt.ml state_monad.ml state.ml testout_types.ml testout.ml test.ml -o test &>> "$LOG" && \
    ./test |& tee -a -- "$LOG" || \
      (echo "Failed:"; echo; tail -- "$LOG"; echo; echo)
  fi
done
