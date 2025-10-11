#!/bin/sh

set -eu

export TEST_PAR=4

returncode=0

if [ "$1" = "typecheck" ]; then
    test/typecheck/run_tests.py || returncode=1
elif [ "$1" = "exec" ]; then
    test/ocaml/run_tests.py || returncode=1
    test/c/run_tests.py || returncode=1
elif [ "$1" = "sv" ]; then
    test/sv/run_tests.py || returncode=1
elif [ "$1" = "lean" ]; then
    test/lean/run_tests.py || returncode=1
elif [ "$1" = "prover" ]; then
    test/lem/run_tests.py || returncode=1
    test/smt/run_tests.py || returncode=1
elif [ "$1" = "other" ]; then
    test/lexing/run_tests.py || returncode=1
    test/pattern_completeness/run_tests.py || returncode=1
    test/mono/run_tests.py || returncode=1
    test/sailcov/run_tests.py || returncode=1
    test/format/run_tests.py || returncode=1
    test/oneoff/run_tests.py || returncode=1
    test/float/run_tests.py || returncode=1
elif [ "$1" = "rocq" ]; then
    test/coq/run_tests.py || returncode=1
    test/c/run_tests.py --targets coq || returncode=1
fi

exit $returncode
