#!/bin/sh

set -eu

export OPAMVERBOSE=2

eval `opam config env`

test/run_core_tests.sh
