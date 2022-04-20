#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAIL=${SAIL:=sail}

mkdir -p $DIR/rtpass
mkdir -p $DIR/rtpass2

rm -f $DIR/tests.xml

printf "\$SAIL is $SAIL\n"

# shellcheck source=../test_helpers.sh
source "$DIR/../test_helpers.sh"

printf "<testsuites>\n" >> $DIR/tests.xml

for i in `ls $DIR/pass/ | grep sail`;
do
    if $SAIL -no_memo_z3 -just_check -ddump_tc_ast $DIR/pass/$i 2> /dev/null 1> $DIR/rtpass/$i;
    then
	if $SAIL -no_memo_z3 -just_check -ddump_tc_ast -dmagic_hash -dno_cast $DIR/rtpass/$i 2> /dev/null 1> $DIR/rtpass2/$i;
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
	if $SAIL -no_memo_z3 ${i%.sail}/$(basename $file) 2> result;
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

for file in $DIR/fail/*.sail;
do
    pushd $DIR/fail > /dev/null;
    if $SAIL -no_memo_z3 $(basename $file) 2> result
    then
        red "Expected failure, but $(basename $file) passed" "fail"
    else
        if diff ${file%.sail}.expect result;
        then
            green "failing $(basename $file)" "pass"
        else
            yellow "failing $(basename $file)" "unexpected error"
        fi
    fi;
    rm -f result;
    popd > /dev/null
done

finish_suite "Typechecking tests"

printf "</testsuites>\n" >> $DIR/tests.xml
