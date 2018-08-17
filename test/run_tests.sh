#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $DIR

printf "\n==========================================\n"
printf "Typechecking tests\n"
printf "==========================================\n"

./typecheck/run_tests.sh

printf "\n==========================================\n"
printf "Ocaml tests\n"
printf "==========================================\n"

./ocaml/run_tests.sh

printf "\n==========================================\n"
printf "C tests\n"
printf "==========================================\n"

./c/run_tests.py

printf "\n==========================================\n"
printf "Lem tests\n"
printf "==========================================\n"

./lem/run_tests.sh

printf "\n==========================================\n"
printf "Builtins tests\n"
printf "==========================================\n"

./builtins/run_tests.py

printf "\n==========================================\n"
printf "ARM spec tests\n"
printf "==========================================\n"

./arm/run_tests.sh

printf "\n==========================================\n"
printf "RISCV spec tests\n"
printf "==========================================\n"

./riscv/run_tests.sh

printf "\n==========================================\n"
printf "CHERI spec tests\n"
printf "==========================================\n"

./cheri/run_tests.sh
