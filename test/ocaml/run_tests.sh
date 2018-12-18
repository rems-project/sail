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

for i in `ls -d */`;
do
    cd $DIR/$i;
    if $SAILDIR/sail -no_warn -o out -ocaml ../prelude.sail `ls *.sail` 1> /dev/null;
    then
	./out > result;
	if diff expect result;
	then
	    green "built $i" "ok"
	else
	    yellow "bad output $i" "fail"
	fi;
	rm out;
	rm result;
	rm -r _sbuild
    else
	red "building $i" "fail"
    fi
done

finish_suite "Ocaml testing"

cd $DIR

for i in `ls -d */`;
do
    cd $DIR/$i;
    if $SAILDIR/sail -no_warn -o out -ocaml -trace ../prelude.sail `ls *.sail` 1> /dev/null;
    then
	./out > result 2> /dev/null;
	if diff expect result;
	then
	    green "built $i" "ok"
	else
	    red "bad output $i" "fail"
	fi;
	rm out;
	rm result;
	rm -r _sbuild
    else
	red "building $i" "fail"
    fi
done

finish_suite "Ocaml trace testing"

cd $DIR

for i in `ls -d */`;
do
    cd $DIR/$i;
    if $SAILDIR/sail -no_warn -is test.isail ../prelude.sail `ls *.sail` 1> /dev/null;
    then
	if diff expect result;
	then
	    green "interpreted $i" "ok"
	else
	    red "bad output $i" "fail"
	fi;
	rm result
    else
	red "interpreter crashed on $i" "fail"
    fi
done

finish_suite "Interpreter testing"

printf "</testsuites>\n" >> $DIR/tests.xml
