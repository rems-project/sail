#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $DIR

./run_core_tests.sh

printf "\n==========================================\n"
printf "Lem tests\n"
printf "==========================================\n"

./lem/run_tests.py

printf "\n==========================================\n"
printf "Monomorphisation tests\n"
printf "==========================================\n"

./mono/run_tests.sh

printf "\n==========================================\n"
printf "LaTeX tests\n"
printf "==========================================\n"

./latex/run_tests.sh

printf "\n==========================================\n"
printf "C tests\n"
printf "==========================================\n"

TEST_PAR=8 ./c/run_tests.py

printf "\n==========================================\n"
printf "SMT tests\n"
printf "==========================================\n"

TEST_PAR=8 ./smt/run_tests.py

printf "\n==========================================\n"
printf "Builtins tests\n"
printf "==========================================\n"

TEST_PAR=4 ./builtins/run_tests.py

printf "\n==========================================\n"
printf "ARM spec tests\n"
printf "==========================================\n"

./arm/run_tests.sh

# This specification has bitrotted
#
# printf "\n==========================================\n"
# printf "aarch64_small spec tests\n"
# printf "==========================================\n"
# 
# ./aarch64_small/run_tests.sh

