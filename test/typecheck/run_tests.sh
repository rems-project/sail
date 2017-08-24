#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

mkdir -p $DIR/rtpass
mkdir -p $DIR/rtpass2
mkdir -p $DIR/lem
mkdir -p $DIR/rtfail

rm -f $DIR/tests.xml

MIPS="$SAILDIR/mips_new_tc"

cat $SAILDIR/lib/prelude.sail $SAILDIR/lib/prelude_wrappers.sail $MIPS/mips_prelude.sail > $DIR/pass/mips_prelude.sail
cat $SAILDIR/lib/prelude.sail $SAILDIR/lib/prelude_wrappers.sail $MIPS/mips_prelude.sail $MIPS/mips_tlb.sail > $DIR/pass/mips_tlb.sail
cat $SAILDIR/lib/prelude.sail $SAILDIR/lib/prelude_wrappers.sail $MIPS/mips_prelude.sail $MIPS/mips_tlb.sail $MIPS/mips_wrappers.sail > $DIR/pass/mips_wrappers.sail
cat $SAILDIR/lib/prelude.sail $SAILDIR/lib/prelude_wrappers.sail $MIPS/mips_prelude.sail $MIPS/mips_tlb.sail $MIPS/mips_wrappers.sail $MIPS/mips_insts.sail $MIPS/mips_epilogue.sail > $DIR/pass/mips_insts.sail
cat $SAILDIR/lib/prelude.sail $SAILDIR/lib/prelude_wrappers.sail $MIPS/mips_prelude.sail $MIPS/mips_tlb_stub.sail $MIPS/mips_wrappers.sail $MIPS/mips_insts.sail $MIPS/mips_epilogue.sail > $DIR/pass/mips_notlb.sail

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
    printf "$XML" >> $DIR/tests.xml
    XML=""
    pass=0
    fail=0
}

printf "<testsuites>\n" >> $DIR/tests.xml

for i in `ls $DIR/pass/`;
do
    if $SAILDIR/sail -ddump_tc_ast -just_check $DIR/pass/$i 2> /dev/null 1> $DIR/rtpass/$i;
    then
	if $SAILDIR/sail -dno_cast -ddump_tc_ast -just_check $DIR/rtpass/$i 2> /dev/null 1> $DIR/rtpass2/$i;
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
    fi
done

finish_suite "Expecting pass"

for i in `ls $DIR/fail/`;
do
    if $SAILDIR/sail -ddump_tc_ast -just_check $DIR/fail/$i 2> /dev/null 1> $DIR/rtfail/$i;
    then
	red "tested $i expecting fail" "pass"
    else
	if $SAILDIR/sail -dno_cast -just_check $DIR/rtfail/$i 2> /dev/null;
	then
	    yellow "tested $i expecting fail" "passed re-check"
	else
	    green "tested $i expecting fail" "fail"
	fi
    fi
done

finish_suite "Expecting fail"

function test_lem {
    for i in `ls $DIR/pass/`;
    do
	# MIPS requires an additional library, Mips_extras_embed.
	# It might be useful to allow adding options for specific test cases.
	# For now, include the library for all test cases, which doesn't seem to hurt.
	if $SAILDIR/sail -lem -lem_lib Mips_extras_embed $DIR/$1/$i 2> /dev/null
	then
	    green "generated lem for $1/$i" "pass"

	    cp $MIPS/mips_extras_embed_sequential.lem $DIR/lem/
	    mv $SAILDIR/${i%%.*}_embed_types.lem $DIR/lem/
	    mv $SAILDIR/${i%%.*}_embed_types_sequential.lem $DIR/lem/
	    mv $SAILDIR/${i%%.*}_embed.lem $DIR/lem/
	    mv $SAILDIR/${i%%.*}_embed_sequential.lem $DIR/lem/
	    # Test sequential embedding for now
	    # TODO: Add tests for the free monad
	    if lem -lib $SAILDIR/src/lem_interp -lib $SAILDIR/src/gen_lib/ $DIR/lem/mips_extras_embed_sequential.lem $DIR/lem/${i%%.*}_embed_types_sequential.lem $DIR/lem/${i%%.*}_embed_sequential.lem 2> /dev/null
	    then
		green "typechecking lem for $1/$i" "pass"
	    else
		red "typechecking lem for $1/$i" "fail"
	    fi
	else
	    red "generated lem for $1/$i" "fail"
	    red "typechecking lem for $1/$i" "fail"
	fi
    done
}

test_lem pass

finish_suite "Lem generation 1"

test_lem rtpass

finish_suite "Lem generation 2"

function test_ocaml {
    for i in `ls $DIR/pass/`;
    do
	if $SAILDIR/sail -ocaml $DIR/$1/$i 2> /dev/null
	then
	    green "generated ocaml for $1/$i" "pass"

	    rm $SAILDIR/${i%%.*}.ml
	else
	    red "generated ocaml for $1/$i" "fail"
	fi
    done
}

test_ocaml pass

finish_suite "Ocaml generation 1"

test_ocaml rtpass

finish_suite "Ocaml generation 2"

printf "</testsuites>\n" >> $DIR/tests.xml
