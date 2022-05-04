#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAIL=${SAIL:=sail}
TESTSDIR="$DIR/../typecheck/pass"

rm -f $DIR/tests.xml

printf "\$SAIL is $SAIL\n"

# shellcheck source=../test_helpers.sh
source "$DIR/../test_helpers.sh"

printf "<testsuites>\n" >> $DIR/tests.xml

cd $DIR

for i in `ls $TESTSDIR/ | grep sail`;
do
    if $SAIL -lem -o out $TESTSDIR/$i &>/dev/null;
    then
	if lem -lib $DIR/../../src2/lib/lem out_types.lem out.lem &>/dev/null;
	then
	    green "tested $i expecting pass" "pass"
	else
	    yellow "tested $i expecting pass" "failed to typecheck generated Lem"
	fi
    else
	red "tested $i expecting pass" "failed to generate Lem"
    fi
done

finish_suite "LEM tests"

printf "</testsuites>\n" >> $DIR/tests.xml
