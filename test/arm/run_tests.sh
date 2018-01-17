#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
SAILDIR="$DIR/../.."

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

rm -f $DIR/tests.xml

pass=0
fail=0
XML=""

function green {
    (( pass += 1 ))
    printf "$1: ${GREEN}$2${NC}\n"
    XML+="    <testcase name=\"$1\"/>\n"
}

function yellow {
    (( fail += 1 ))
    printf "$1: ${YELLOW}$2${NC}\n"
    XML+="    <testcase name=\"$1\">\n      <error message=\"$2\">$2</error>\n    </testcase>\n"
}

function red {
    (( fail += 1 ))
    printf "$1: ${RED}$2${NC}\n"
    XML+="    <testcase name=\"$1\">\n      <error message=\"$2\">$2</error>\n    </testcase>\n"
}

function finish_suite {
    printf "$1: Passed ${pass} out of $(( pass + fail ))\n\n"
    XML="  <testsuite name=\"$1\" tests=\"$(( pass + fail ))\" failures=\"${fail}\" timestamp=\"$(date)\">\n$XML  </testsuite>\n"
    printf "$XML" >> $DIR/tests.xml
    XML=""
    pass=0
    fail=0
}

SAILLIBDIR="$DIR/../../lib/"

printf "<testsuites>\n" >> $DIR/tests.xml

cd $SAILDIR/aarch64

printf "Compiling specification...\n"

if $SAILDIR/sail -o aarch64_test -ocaml prelude.sail no_vector/spec.sail decode_start.sail no_vector/decode.sail decode_end.sail main.sail 1> /dev/null;
then
    green "compiled no_vector specification" "ok";
    mv aarch64_test $DIR/;
    cd $DIR;

    for i in `ls *.elf`;
    do
	$DIR/aarch64_test $i 2> /dev/null 1> ${i%.elf}.result
	if diff ${i%.elf}.result ${i%.elf}.expect;
	then
	    green "ran $i" "ok"
	else
	    red "failed $i" "fail"
	fi;
	rm -f *.result
    done;

    rm -f aarch64_test
else
    red "compiling no_vector specification" "fail";

    for $i in `ls *.elf`;
    do
	red "failed $i" "fail"
    done
fi

finish_suite "ARM generated spec tests"

printf "</testsuites>\n" >> $DIR/tests.xml
