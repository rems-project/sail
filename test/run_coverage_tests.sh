#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd "$DIR"

returncode=0

printf "\n==========================================\n"
printf "Lexing tests\n"
printf "==========================================\n"

./suites/runner.py -s lexing || returncode=1

printf "\n==========================================\n"
printf "Pattern completeness tests\n"
printf "==========================================\n"

./suites/runner.py -s pattern_completeness || returncode=1

printf "\n==========================================\n"
printf "Typechecking tests\n"
printf "==========================================\n"

./suites/runner.py -s typecheck || returncode=1

printf "\n==========================================\n"
printf "OCaml tests\n"
printf "==========================================\n"

./suites/runner.py -s ocaml || returncode=1

printf "\n==========================================\n"
printf "Lem tests\n"
printf "==========================================\n"

./suites/runner.py -s lem || returncode=1

printf "\n==========================================\n"
printf "Exec tests\n"
printf "==========================================\n"

./suites/runner.py -s exec.c -s exec.cpp -s exec.interpreter -s exec.ocaml -s exec.partial || returncode=1

printf "\n==========================================\n"
printf "SMT tests\n"
printf "==========================================\n"

./suites/runner.py -s smt || returncode=1

printf "\n==========================================\n"
printf "SystemVerilog tests\n"
printf "==========================================\n"

verilator --version || returncode=1

./suites/runner.py -s sv || returncode=1

printf "\n==========================================\n"
printf "Lean tests\n"
printf "==========================================\n"

./suites/runner.py -s lean || returncode=1

printf "\n==========================================\n"
printf "sailcov tests\n"
printf "==========================================\n"

./suites/runner.py -s sailcov || returncode=1

printf "\n==========================================\n"
printf "Formatting tests\n"
printf "==========================================\n"

./suites/runner.py -s format || returncode=1

printf "\n==========================================\n"
printf "One-off tests\n"
printf "==========================================\n"

./suites/runner.py -s oneoff || returncode=1

exit $returncode
