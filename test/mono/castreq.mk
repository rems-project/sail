#!/bin/sh
set -ex
sail ../../aarch64/prelude.sail ../../lib/mono_rewrites.sail castreq.sail -verbose -auto_mono -lem -lem_mwords -lem_sequential -lem_lib Aarch64_extras_embed -o x -undefined_gen
lem -lib ../../src/gen_lib/ -lib ../../src/lem_interp -lib ~/local/rems/2018-01-aarch64/aarch64/ x_embed_sequential.lem 
