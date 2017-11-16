#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $DIR/..
./test/typecheck/run_tests.sh
./test/ocaml/run_tests.sh
