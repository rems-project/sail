#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."

RED='\033[0;91m'
GREEN='\033[0;92m'
YELLOW='\033[0;93m'
NC='\033[0m'

mkdir -p $DIR/rtpass
mkdir -p $DIR/rtpass2

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

for i in `ls $DIR/pass/ | grep sail`;
do
    if $SAILDIR/sail -just_check -ddump_tc_ast -dsanity $DIR/pass/$i 2> /dev/null 1> $DIR/rtpass/$i;
    then
	if $SAILDIR/sail -just_check -ddump_tc_ast -dmagic_hash -dno_cast -dsanity $DIR/rtpass/$i 2> /dev/null 1> $DIR/rtpass2/$i;
	then
	    if diff $DIR/rtpass/$i $DIR/rtpass2/$i;
	    then
		green "tested $i expecting pass" "pass"
	    else
		yellow "tested $i expecting pass" "re-check AST was different"
	    fi
	else
	    yellow "tested $i expecting pass" "failed re-check"
	fi
    else
	red "tested $i expecting pass" "fail"
    fi;

    shopt -s nullglob;
    for file in $DIR/pass/${i%.sail}/*.sail;
    do
	pushd $DIR/pass > /dev/null;
	if $SAILDIR/sail ${i%.sail}/$(basename $file) 2> result;
	then
	    red "failing variant of $i $(basename $file) passed" "fail"
	else
	    if diff ${file%.sail}.expect result;
	    then
		green "failing variant of $i $(basename $file)" "pass"
	    else
		yellow "failing variant of $i $(basename $file)" "unexpected error"
	    fi
	fi;
	rm -f result;
	popd > /dev/null
    done
done

finish_suite "Typechecking tests"

printf "</testsuites>\n" >> $DIR/tests.xml
