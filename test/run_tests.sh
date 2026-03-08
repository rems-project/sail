#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd "$DIR"

./run_core_tests.sh

printf "\n==========================================\n"
printf "Lem tests\n"
printf "==========================================\n"

./suites/lem.py

printf "\n==========================================\n"
printf "Monomorphisation tests\n"
printf "==========================================\n"

./suites/mono.py

printf "\n==========================================\n"
printf "LaTeX tests\n"
printf "==========================================\n"

./latex/run_tests.sh

printf "\n==========================================\n"
printf "Exec tests\n"
printf "==========================================\n"

TEST_PAR=8 ./suites/exec.py

printf "\n==========================================\n"
printf "SMT tests\n"
printf "==========================================\n"

TEST_PAR=8 ./suites/smt.py

printf "\n==========================================\n"
printf "Builtins tests\n"
printf "==========================================\n"

TEST_PAR=4 ./suites/builtins.py

printf "\n==========================================\n"
printf "ARM spec tests\n"
printf "==========================================\n"

./arm/run_tests.sh

printf "\n==========================================\n"
printf "Lean tests\n"
printf "==========================================\n"

./suites/lean.py

# This specification has bitrotted
#
# printf "\n==========================================\n"
# printf "aarch64_small spec tests\n"
# printf "==========================================\n"
# 
# ./aarch64_small/run_tests.sh

