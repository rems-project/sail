#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

$DIR/typecheck/run_tests.sh
$DIR/ocaml/run_tests.sh
