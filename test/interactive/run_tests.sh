#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAIL=${SAIL:=sail}

rm -f $DIR/tests.xml

printf "\$SAIL is $SAIL\n"

# shellcheck source=../test_helpers.sh
source "$DIR/../test_helpers.sh"

printf "<testsuites>\n" >> $DIR/tests.xml

for i in `ls $DIR/pass/ | grep '\.isail$'`;
do
    source=`echo $i | sed -e 's/^\(.*[^0-9]\)[0-9]*\.isail$/\1.sail/'`
    expected=`basename -s .isail $i`.expected
    if $SAIL $DIR/pass/$source -is $DIR/pass/$i;
    then
        if grep -v '^overload\|\$include' out.sail | diff - $DIR/pass/$expected;
	then
	    green "tested $i expecting pass" "pass"
	else
	    yellow "tested $i expecting pass" "AST was different"
	fi
    else
	red "tested $i expecting pass" "fail"
    fi;
done

finish_suite "Interactive command tests"

printf "</testsuites>\n" >> $DIR/tests.xml
