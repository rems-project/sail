#!/bin/sh

set -e

# -auto_mono lifts the size expression in Mem_write_request into a record
# parameter; the sail_mem_write outcome's signature must be rewritten to match.
sail --lem --lem-mwords --auto-mono -o out test.sail
rm -f out.lem out_types.lem Out_lemmas.thy
