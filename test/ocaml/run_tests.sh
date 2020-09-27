#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
SAILDIR="$DIR/../.."

rm -f $DIR/tests.xml

# shellcheck source=../test_helpers.sh
source "$SAILDIR/test/test_helpers.sh"

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

# FIXME: Renable these!
#cd $DIR
#
#for i in `ls -d */`;
#do
#    cd $DIR/$i;
#    if $SAILDIR/sail -no_warn -undefined_gen -is test.isail ../prelude.sail `ls *.sail` 1> /dev/null;
#    then
#	if diff expect result;
#	then
#	    green "interpreted $i" "ok"
#	else
#	    red "bad output $i" "fail"
#	fi;
#	rm result
#    else
#	red "interpreter crashed on $i" "fail"
#    fi
#done
#
#finish_suite "Interpreter testing"

printf "</testsuites>\n" >> $DIR/tests.xml
