#!/usr/bin/env bash
set -e

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'


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
    printf "$1: Passed ${pass} out of $(( pass + fail ))\n"
    XML="  <testsuite name=\"$1\" tests=\"$(( pass + fail ))\" failures=\"${fail}\" timestamp=\"$(date)\">\n$XML  </testsuite>\n"
    printf "$XML" > $1.xml
    XML=""
    pass=0
    fail=0
}

test_regex="^(.*): (pass|fail)$"
while read line; do
    if [[ $line =~ $test_regex ]] ; then
        test_name=${BASH_REMATCH[1]}
        test_status=${BASH_REMATCH[2]}
        if [[ $test_status == pass ]] ; then
            green $test_name $test_status
        else
            red $test_name $test_status
        fi
    else
        echo $line
    fi
done
finish_suite all_tests
