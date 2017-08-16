#!/bin/bash

set -ex

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."
LEMDIR="$DIR/../../../lem"
OUTDIR="$DIR/fnreduce-ml"
ZARITH="$LEMDIR/ocaml-lib/dependencies/zarith"

"$SAILDIR/sail" -lem "$SAILDIR/lib/prelude.sail" -mono-split fnreduce.sail:43:x "$DIR/fnreduce.sail" -o "$DIR/fnreduce"
if [ -d "$OUTDIR" ]; then
  rm -- "$OUTDIR"/*
else
  mkdir -- "$OUTDIR"
fi
"$LEMDIR/bin/lem" -ocaml -lib "$SAILDIR/src/lem_interp" "$SAILDIR/src/gen_lib/sail_values.lem" "$SAILDIR/src/gen_lib/state.lem" "$DIR/fnreduce_embed_types.lem" "$DIR/fnreduce_embed_sequential.lem" -outdir "$OUTDIR"
cp -- "$DIR"/test.ml "$OUTDIR"
cd "$OUTDIR"
ocamlc -I "$ZARITH" "$ZARITH/zarith.cma" -dllpath "$ZARITH" -I "$LEMDIR/ocaml-lib" "$LEMDIR/ocaml-lib/extract.cma" -I "$SAILDIR/src/_build/lem_interp" "$SAILDIR/src/_build/lem_interp/extract.cma" sail_values.ml state.ml fnreduce_embed_types.ml fnreduce_embed_sequential.ml test.ml -o test
./test
