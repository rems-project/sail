#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd "$DIR"

returncode=0

printf "\n==========================================\n"
printf "Lexing tests\n"
printf "==========================================\n"

./suites/lexing.py || returncode=1

printf "\n==========================================\n"
printf "Pattern completeness tests\n"
printf "==========================================\n"

./suites/pattern_completeness.py || returncode=1

printf "\n==========================================\n"
printf "Typechecking tests\n"
printf "==========================================\n"

./suites/typecheck.py || returncode=1

printf "\n==========================================\n"
printf "OCaml tests\n"
printf "==========================================\n"

./suites/ocaml.py || returncode=1

printf "\n==========================================\n"
printf "Lem tests\n"
printf "==========================================\n"

./suites/lem.py || returncode=1

printf "\n==========================================\n"
printf "Exec tests\n"
printf "==========================================\n"

./suites/exec.py || returncode=1

printf "\n==========================================\n"
printf "SMT tests\n"
printf "==========================================\n"

./suites/smt.py || returncode=1

printf "\n==========================================\n"
printf "SystemVerilog tests\n"
printf "==========================================\n"

verilator --version || returncode=1

./suites/sv.py || returncode=1

printf "\n==========================================\n"
printf "Lean tests\n"
printf "==========================================\n"

./suites/lean.py || returncode=1

printf "\n==========================================\n"
printf "sailcov tests\n"
printf "==========================================\n"

./suites/sailcov.py || returncode=1

printf "\n==========================================\n"
printf "Formatting tests\n"
printf "==========================================\n"

./suites/format.py || returncode=1

printf "\n==========================================\n"
printf "One-off tests\n"
printf "==========================================\n"

./suites/oneoff.py || returncode=1

exit $returncode
