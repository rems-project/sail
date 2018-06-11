
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

printf "<testsuites>\n" >> $DIR/tests.xml

shopt -s nullglob;

function run_c_tests {
    for file in $DIR/*.sail;
    do
	if $SAILDIR/sail -no_warn -c $SAIL_OPTS $file 1> ${file%.sail}.c 2> /dev/null;
	then
	    green "compiling $(basename $file) ($SAIL_OPTS)" "ok";
	    if gcc $CC_OPTS ${file%.sail}.c -lgmp -I $SAILDIR/lib;
	    then
		green "compiling $(basename ${file%.sail}.c) ($CC_OPTS)" "ok";
		$DIR/a.out 1> ${file%.sail}.result 2> /dev/null;
		if diff ${file%.sail}.result ${file%.sail}.expect;
		then
		    green "executing $(basename ${file%.sail})" "ok"
		else
		    red "executing $(basename ${file%.sail})" "fail"
		fi;
		if valgrind -q --leak-check=full --errors-for-leak-kinds=all --error-exitcode=1 $DIR/a.out 1> /dev/null 2> /dev/null;
		then
		    green "executing $(basename ${file%.sail}) with valgrind" "ok"
		else
		    red "executing $(basename ${file%.sail}) with valgrind" "fail"
		fi
	    else
		red "compiling generated C" "fail"
	    fi
	else
	    red "compiling $file" "fail"
	fi;
	rm -f ${file%.sail}.c
	rm -f ${file%.sail}.result
    done
}

SAIL_OPTS=""
CC_OPTS="-O0"
run_c_tests

SAIL_OPTS="-O"
CC_OPTS="-O2"
run_c_tests

SAIL_OPTS="-O"
CC_OPTS="-O2 -fsanitize=undefined"
run_c_tests

finish_suite "C testing"

printf "</testsuites>\n" >> $DIR/tests.xml
