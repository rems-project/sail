#!/bin/sh

if [ "$#" -ne 1 ]; then
    echo "Illegal number of parameters"
    echo "Usage: 1 arg (name of coq module to consider without .v extension)"
    exit 1
fi

infile="theories/$1.v"
outfile="$1_print_assumptions.v"

echo "Require Import bbv.$1." > "$outfile"

grep -E "$infile" -e '^ *(Lemma|Theorem|Corollary)' | grep -v 'Note: not axiom free' | sed -E -e 's/ *(Lemma|Theorem|Corollary) //g' -e 's/^([^ :]+).*/About \1. Print Assumptions \1./g' >> "$outfile"
