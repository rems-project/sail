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
while read -u 3 TEST ARGS; do
  if [ -z "$TESTONLY" -o "$TEST" = "$TESTONLY" ]; then
#    echo "$TEST ocaml"
#    rm -f -- "$OUTDIR"/*
#    "$SAILDIR/sail" -ocaml "$SAILDIR/lib/prelude.sail" "$DIR/$TEST" -o "$OUTDIR/testout" $ARGS
#    cp -- "$SAILDIR"/src/gen_lib/sail_values.ml .
#    cp -- "$DIR"/test.ml .
#    ocamlc -I "$ZARITH" "$ZARITH/zarith.cma" -dllpath "$ZARITH" -I "$LEMDIR/ocaml-lib" "$LEMDIR/ocaml-lib/extract.cma" -I "$SAILDIR/src/_build/lem_interp" "$SAILDIR/src/_build/lem_interp/extract.cma" sail_values.ml testout.ml test.ml -o test
#    ./test
   
    echo "$TEST lem - ocaml" | tee -a -- "$LOG"
    rm -f -- "$OUTDIR"/*
    "$SAILDIR/sail" -lem "$SAILDIR/lib/prelude.sail" "$DIR/$TEST".sail -o "$OUTDIR/testout" $ARGS $@ &>> "$LOG"
    "$LEMDIR/bin/lem" -ocaml -lib "$SAILDIR/src/lem_interp" "$SAILDIR/src/gen_lib/sail_values.lem" "$SAILDIR/src/gen_lib/sail_operators_mwords.lem" "$SAILDIR/src/gen_lib/state.lem" testout_embed_types_sequential.lem testout_embed_sequential.lem -outdir "$OUTDIR" &>> "$LOG"
    cp -- "$DIR"/test.ml "$OUTDIR"
    ocamlc -I "$ZARITH" "$ZARITH/zarith.cma" -dllpath "$ZARITH" -I "$LEMDIR/ocaml-lib" "$LEMDIR/ocaml-lib/extract.cma" -I "$SAILDIR/src/_build/lem_interp" "$SAILDIR/src/_build/lem_interp/extract.cma" sail_values.ml sail_operators_mwords.ml state.ml testout_embed_types_sequential.ml testout_embed_sequential.ml test.ml -o test &>> "$LOG"
    ./test |& tee -a -- "$LOG" || tail -- "$LOG"
  fi
done
