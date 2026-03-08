#!/bin/sh

set -eu

export TEST_PAR=4

returncode=0

if [ "$1" = "typecheck" ]; then
    test/suites/typecheck.py || returncode=1
elif [ "$1" = "exec" ]; then
    test/suites/ocaml.py || returncode=1
    test/suites/exec.py || returncode=1
elif [ "$1" = "sv" ]; then
    test/suites/sv.py || returncode=1
elif [ "$1" = "lean" ]; then
    test/suites/lean.py || returncode=1
elif [ "$1" = "prover" ]; then
    test/suites/lem.py || returncode=1
    test/suites/smt.py || returncode=1
elif [ "$1" = "other" ]; then
    test/suites/lexing.py || returncode=1
    test/suites/pattern_completeness.py || returncode=1
    test/suites/mono.py || returncode=1
    test/suites/sailcov.py || returncode=1
    test/suites/format.py || returncode=1
    test/suites/oneoff.py || returncode=1
    test/suites/float.py || returncode=1
elif [ "$1" = "rocq" ]; then
    test/suites/coq.py || returncode=1
    test/suites/exec.py --targets coq || returncode=1
fi

exit $returncode
