#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

mkdir -p $DIR/rtpass
mkdir -p $DIR/rtfail

pass=0
fail=0

for i in `ls $DIR/pass/`;
do
    printf "testing $i expecting pass: "
    if $DIR/../../sail -ddump_tc_ast -just_check $DIR/pass/$i 2> /dev/null 1> $DIR/rtpass/$i;
    then
	if $DIR/../../sail -dno_cast -just_check $DIR/rtpass/$i 2> /dev/null;
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
    if $DIR/../../sail -ddump_tc_ast -just_check $DIR/fail/$i 2> /dev/null 1> $DIR/rtfail/$i;
    then
	(( fail += 2 ))
	printf "${RED}pass${NC}\n"
    else
	if $DIR/../../sail -dno_cast -just_check $DIR/rtfail/$i 2> /dev/null;
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

printf "Passed ${pass} out of $(( pass + fail ))\n"
