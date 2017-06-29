#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

mkdir -p $DIR/rtpass
mkdir -p $DIR/rtfail

for i in `ls $DIR/pass/`;
do
    printf "testing $i expecting pass: "
    if $DIR/../../sail -ddump_tc_ast -just_check $DIR/pass/$i 2> /dev/null 1> $DIR/rtpass/$i;
    then
	if $DIR/../../sail -dno_cast -just_check $DIR/rtpass/$i 2> /dev/null;
	then
	    printf "${GREEN}pass${NC}\n"
	else
	    printf "${YELLOW}pass${NC}\n"
	fi
    else
	printf "${RED}fail${NC}\n"
    fi
done

for i in `ls $DIR/fail/`;
do
    printf "testing $i expecting fail: "
    if $DIR/../../sail -ddump_tc_ast -just_check $DIR/fail/$i 2> /dev/null 1> $DIR/rtfail/$i;
    then
	printf "${RED}pass${NC}\n"
    else
	if $DIR/../../sail -dno_cast -just_check $DIR/rtfail/$i 2> /dev/null;
	then
	    printf "${YELLOW}fail${NC}\n"
	else
	    printf "${GREEN}fail${NC}\n"
	fi
    fi
done
