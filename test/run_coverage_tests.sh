#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $DIR

returncode=0

printf "\n==========================================\n"
printf "Lexing tests\n"
printf "==========================================\n"

./lexing/run_tests.py || returncode=1

printf "\n==========================================\n"
printf "Pattern completeness tests\n"
printf "==========================================\n"

./pattern_completeness/run_tests.py || returncode=1

printf "\n==========================================\n"
printf "Typechecking tests\n"
printf "==========================================\n"

./typecheck/run_tests.py || returncode=1

printf "\n==========================================\n"
printf "OCaml tests\n"
printf "==========================================\n"

./ocaml/run_tests.sh || returncode=1

printf "\n==========================================\n"
printf "Lem tests\n"
printf "==========================================\n"

./lem/run_tests.py || returncode=1

printf "\n==========================================\n"
printf "C tests\n"
printf "==========================================\n"

./c/run_tests.py || returncode=1

printf "\n==========================================\n"
printf "SMT tests\n"
printf "==========================================\n"

./smt/run_tests.py || returncode=1

printf "\n==========================================\n"
printf "Formatting tests\n"
printf "==========================================\n"

./format/run_tests.py || returncode=1

exit $returncode
