#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $DIR

printf "\n==========================================\n"
printf "Typechecking tests\n"
printf "==========================================\n"

./typecheck/run_tests.sh

printf "\n==========================================\n"
printf "Lem tests\n"
printf "==========================================\n"

./lem/run_tests.sh

printf "\n==========================================\n"
printf "Ocaml tests\n"
printf "==========================================\n"

./ocaml/run_tests.sh

printf "\n==========================================\n"
printf "C tests\n"
printf "==========================================\n"

TEST_PAR=8 ./c/run_tests.py

printf "\n==========================================\n"
printf "Builtins tests\n"
printf "==========================================\n"

TEST_PAR=4 ./builtins/run_tests.py

printf "\n==========================================\n"
printf "ARM spec tests\n"
printf "==========================================\n"

./arm/run_tests.sh

