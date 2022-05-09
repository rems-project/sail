#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
SAILDIR="$DIR/../.."
SAIL=${SAIL:=sail}

rm -f $DIR/tests.xml

printf "\$SAIL is $SAIL\n"

# shellcheck source=../test_helpers.sh
source "$SAILDIR/test/test_helpers.sh"

printf "<testsuites>\n" >> $DIR/tests.xml

if make -B -C ../../aarch64_small armV8.lem SAIL="$SAIL"
then
    green "built aarch64_small to lem" "ok"
else
    red "failed to build lem" "fail"
fi

if make -B -C ../../aarch64_small armV8.smt_model SAIL="$SAIL"
then
    green "compiled aarch64_small for SMT generation" "ok"
else
    red "failed to build aarch64_small for SMT generation" "fail"
fi

finish_suite "aarch64_small tests"

printf "</testsuites>\n" >> $DIR/tests.xml
