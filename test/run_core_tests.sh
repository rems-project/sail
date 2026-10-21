#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd "$DIR"

# Some basic tests that don't have external tool requirements, don't
# take too long, and don't have regressions that we haven't sorted out
# yet.

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
printf "Floating point tests\n"
printf "==========================================\n"

./suites/runner.py -s float || returncode=1

printf "\n==========================================\n"
printf "Plugin tests\n"
printf "==========================================\n"

./suites/runner.py -s plugins || returncode=1

exit $returncode
