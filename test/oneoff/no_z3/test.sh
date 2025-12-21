#!/bin/sh

set -e

rm -f no_z3.result
SAIL="$(which sail)"
GREP="$(which grep)"
export PATH=""
$SAIL --version 2> no_z3.result || true
$GREP "SMT solver returned unexpected status" no_z3.result
