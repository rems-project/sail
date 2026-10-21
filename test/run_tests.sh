#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd "$DIR"

./run_core_tests.sh

printf "\n==========================================\n"
printf "Lem tests\n"
printf "==========================================\n"

./suites/runner.py -s lem

printf "\n==========================================\n"
printf "Monomorphisation tests\n"
printf "==========================================\n"

./suites/runner.py -s mono

printf "\n==========================================\n"
printf "LaTeX tests\n"
printf "==========================================\n"

./latex/run_tests.sh

printf "\n==========================================\n"
printf "Exec tests\n"
printf "==========================================\n"

TEST_PAR=8 ./suites/runner.py -s exec.c -s exec.cpp -s exec.interpreter -s exec.ocaml -s exec.partial

printf "\n==========================================\n"
printf "SMT tests\n"
printf "==========================================\n"

TEST_PAR=8 ./suites/runner.py -s smt

printf "\n==========================================\n"
printf "Builtins tests\n"
printf "==========================================\n"

TEST_PAR=4 ./suites/runner.py -s builtins.c -s builtins.ocaml

printf "\n==========================================\n"
printf "ARM spec tests\n"
printf "==========================================\n"

./arm/run_tests.sh

printf "\n==========================================\n"
printf "Lean tests\n"
printf "==========================================\n"

./suites/runner.py -s lean

# This specification has bitrotted
#
# printf "\n==========================================\n"
# printf "aarch64_small spec tests\n"
# printf "==========================================\n"
# 
# ./aarch64_small/run_tests.sh

