#!/bin/sh

set -eu

echo "sail --version: $(sail --version)"

export TEST_PAR=4

test/run_core_tests.sh
