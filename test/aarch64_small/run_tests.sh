#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
SAILDIR="$DIR/../.."

RED='\033[0;91m'
GREEN='\033[0;92m'
YELLOW='\033[0;93m'
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

printf "<testsuites>\n" >> $DIR/tests.xml

if make -B -C ../../aarch64_small armV8.lem SAIL="$SAILDIR/sail" SAILFLAGS="-no_warn"
then
    green "built aarch64_small to lem" "ok"
else
    red "failed to build lem" "fail"
fi

if make -B -C ../../aarch64_small armV8.smt_model SAIL="$SAILDIR/sail" SAILFLAGS="-no_warn"
then
    green "compiled aarch64_small for SMT generation" "ok"
else
    red "failed to build aarch64_small for SMT generation" "fail"
fi

finish_suite "aarch64_small tests"

printf "</testsuites>\n" >> $DIR/tests.xml
