#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."
TESTSDIR="$DIR/../typecheck/pass"

rm -f $DIR/tests.xml

# shellcheck source=../test_helpers.sh
source "$SAILDIR/test/test_helpers.sh"

printf "<testsuites>\n" >> $DIR/tests.xml

cd $DIR

for i in `ls $TESTSDIR/ | grep sail`;
do
    if $SAILDIR/sail -lem -o out $TESTSDIR/$i &>/dev/null;
    then
	if lem -lib $SAILDIR/src/lem_interp -lib $SAILDIR/src/gen_lib out_types.lem out.lem &>/dev/null;
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
