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

cd $SAILDIR/riscv

printf "Building RISCV specification...\n"

if make -C $SAILDIR/riscv platform ;
then
    green "Building RISCV specification" "ok"
else
    red "Building RISCV specification" "fail"
fi

for test in $DIR/tests/*.elf; do
    if $SAILDIR/riscv/platform "$test" >"${test/.elf/.out}" 2>&1 && grep -q SUCCESS "${test/.elf/.out}"
    then
       green "$(basename $test)" "ok"
    else
       red "$(basename $test)" "fail"
    fi
done

if make -C $SAILDIR/riscv riscv_c;
then
    green "Building RISCV specification to C" "ok"
else
    red "Building RISCV specification to C" "fail"
fi

for test in $DIR/tests/*.elf; do
    $SAILDIR/sail -elf $test -o ${test%.elf}.bin 2> /dev/null;
    if timeout 5 $SAILDIR/riscv/riscv_c --binary=0x1000,reset_vec.bin --image=${test%.elf}.bin > ${test%.elf}.cout 2>&1 && grep -q SUCCESS ${test%.elf}.cout
    then
	green "$(basename $test)" "ok"
    else
	red "$(basename $test)" "fail"
    fi
done

finish_suite "RISCV tests"

printf "</testsuites>\n" >> $DIR/tests.xml

