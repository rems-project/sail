#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
SAILDIR="$DIR/../.."
AARCH64_TEST_DIR="$DIR/../arm"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

rm -f $DIR/tests.xml

# shellcheck source=../test_helpers.sh
source "$SAILDIR/test/test_helpers.sh"

SAILLIBDIR="$DIR/../../lib/"

printf "<testsuites>\n" >> $DIR/tests.xml

printf "Compiling AArch64 specification (Sail->Isabelle->OCaml)...\n"

if make "run_aarch64.native" 1> /dev/null 2> /dev/null;
then
    green "compiled no_vector specification" "ok";

    for i in `ls ${AARCH64_TEST_DIR}/*.elf`;
    do
	$DIR/run_aarch64.native $i 2> /dev/null 1> ${i%.elf}.result
	if diff ${i%.elf}.result ${i%.elf}.expect;
	then
	    green "ran $(basename $i)" "ok"
	else
	    red "failed $(basename $i)" "fail"
	fi;
	rm -f ${i%.elf}.result
    done;
else
    red "compiling no_vector specification" "fail";

    for i in `ls ${AARCH64_TEST_DIR}/*.elf`;
    do
	red "failed $(basename $i)" "fail"
    done
fi

printf "Compiling CHERI specification (Sail->Isabelle->OCaml)...\n"

if make "run_cheri.native" 1> /dev/null 2> /dev/null;
then
    green "compiled CHERI-256 specification" "ok";
else
    red "compiling CHERI-256 specification" "fail";
fi

make clean 1> /dev/null 2> /dev/null

finish_suite "Isabelle code generation tests"

printf "</testsuites>\n" >> $DIR/tests.xml
