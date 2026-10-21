#!/bin/sh

set -eu

export TEST_PAR=4

returncode=0

if [ "$1" = "typecheck" ]; then
    test/suites/runner.py -s typecheck || returncode=1
elif [ "$1" = "exec" ]; then
    test/suites/runner.py -s ocaml || returncode=1
    test/suites/runner.py -s exec.c -s exec.cpp -s exec.interpreter -s exec.ocaml -s exec.partial || returncode=1
elif [ "$1" = "sv" ]; then
    test/suites/runner.py -s sv || returncode=1
elif [ "$1" = "lean" ]; then
    test/suites/runner.py -s lean || returncode=1
elif [ "$1" = "prover" ]; then
    test/suites/runner.py -s lem || returncode=1
    test/suites/runner.py -s smt || returncode=1
elif [ "$1" = "other" ]; then
    test/suites/runner.py -s lexing || returncode=1
    test/suites/runner.py -s pattern_completeness || returncode=1
    test/suites/runner.py -s mono || returncode=1
    test/suites/runner.py -s sailcov || returncode=1
    test/suites/runner.py -s format || returncode=1
    test/suites/runner.py -s oneoff || returncode=1
    test/suites/runner.py -s float || returncode=1
    test/lsp/run_tests.py || returncode=1
elif [ "$1" = "rocq" ]; then
    test/suites/runner.py -s rocq || returncode=1
    test/suites/runner.py -s exec.rocq || returncode=1
fi

exit $returncode
