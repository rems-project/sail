#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."
TESTSDIR="$DIR/../typecheck/pass"

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

printf "<testsuites>\n" >> $DIR/tests.xml

cd $DIR

for i in `ls $TESTSDIR/ | grep sail | grep -vf "$DIR/skip"`;
do
    if $SAILDIR/sail -coq -o out $TESTSDIR/$i &>/dev/null;
    then
	if coqc -R ~/bbv bbv -R ../../../sail-private/coq-duopods/precise/lib Sail out_types.v out.v &>/dev/null;
	then
	    green "tested $i expecting pass" "pass"
	else
	    yellow "tested $i expecting pass" "failed to typecheck generated Coq"
	fi
    else
	red "tested $i expecting pass" "failed to generate Coq"
    fi
done

finish_suite "Coq tests"

printf "</testsuites>\n" >> $DIR/tests.xml
