#!/bin/sh

set -eu

export TEST_PAR=4

test/run_core_tests.sh
