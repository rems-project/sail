#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

mkdir -p $DIR/rtpass
mkdir -p $DIR/lem
mkdir -p $DIR/rtfail

pass=0
fail=0

for i in `ls $DIR/pass/`;
do
    printf "testing $i expecting pass: "
    if $SAILDIR/sail -ddump_tc_ast -just_check $DIR/pass/$i 2> /dev/null 1> $DIR/rtpass/$i;
    then
	if $SAILDIR/sail -dno_cast -just_check $DIR/rtpass/$i 2> /dev/null;
	then
	    (( pass += 2))
	    printf "${GREEN}pass${NC}\n"
	else
	    (( fail += 1 ))
	    (( pass += 1 ))
	    printf "${YELLOW}pass but failed re-check${NC}\n"
	fi
    else
	(( fail += 2 ))
	printf "${RED}fail${NC}\n"
    fi
done

for i in `ls $DIR/fail/`;
do
    printf "testing $i expecting fail: "
    if $SAILDIR/sail -ddump_tc_ast -just_check $DIR/fail/$i 2> /dev/null 1> $DIR/rtfail/$i;
    then
	(( fail += 2 ))
	printf "${RED}pass${NC}\n"
    else
	if $SAILDIR/sail -dno_cast -just_check $DIR/rtfail/$i 2> /dev/null;
	then
	    (( fail += 1 ))
	    (( pass += 1 ))
	    printf "${YELLOW}fail but passed re-check${NC}\n"
	else
	    (( pass += 2 ))
	    printf "${GREEN}fail${NC}\n"
	fi
    fi
done

function test_lem {
    for i in `ls $DIR/pass/`;
    do
	printf "generating lem for $1/$i: "
	if $SAILDIR/sail -lem $DIR/$1/$i 2> /dev/null
	then
	    mv $SAILDIR/${i%%.*}_embed_types.lem $DIR/lem/
	    mv $SAILDIR/${i%%.*}_embed.lem $DIR/lem/
	    mv $SAILDIR/${i%%.*}_embed_sequential.lem $DIR/lem/
	    if lem -lib $SAILDIR/src/lem_interp -lib $SAILDIR/src/gen_lib/ $DIR/lem/${i%%.*}_embed_types.lem $DIR/lem/${i%%.*}_embed.lem 2> /dev/null
	    then
		(( pass += 1 ))
		printf "${GREEN}pass${NC}\n"
	    else
		(( fail += 1 ))
		printf "${RED}fail${NC}\n"
	    fi
	else
	    (( fail += 1 ))
	    printf "${RED}failed to generate lem!${NC}\n"
	fi
    done
}

test_lem pass
test_lem rtpass

printf "Passed ${pass} out of $(( pass + fail ))\n"
