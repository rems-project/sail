#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $DIR

if [ -z "$SAIL_DIR" ]; then
  SAIL_DIR="$DIR/.."
fi
export SAIL_DIR

# Some basic tests that don't have external tool requirements, don't
# take too long, and don't have regressions that we haven't sorted out
# yet.

returncode=0

printf "\n==========================================\n"
printf "Lexing tests\n"
printf "==========================================\n"

./lexing/run_tests.sh || returncode=1

printf "\n==========================================\n"
printf "Typechecking tests\n"
printf "==========================================\n"

./typecheck/run_tests.sh || returncode=1

printf "\n==========================================\n"
printf "OCaml tests\n"
printf "==========================================\n"

./ocaml/run_tests.sh || returncode=1

exit $returncode
