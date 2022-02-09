#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."

# shellcheck source=../test_helpers.sh
source "$SAILDIR/test/test_helpers.sh"

printf "<testsuites>\n" >> $DIR/tests.xml

for file in $DIR/*.sail;
do
    pushd $DIR > /dev/null;
    if $SAILDIR/sail $(basename $file) 2> $DIR/result 1> /dev/null;
    then
        red "tested $(basename $file) expecting error" "fail"
    else
        if diff $DIR/result ${file%.sail}.expect;
        then
            green "tested $(basename $file) expecting error" "pass"
        else
            yellow "tested $(basename $file) expecting error" "unexpected error"
        fi
    fi
    rm $DIR/result;
    popd > /dev/null
done

finish_suite "Lexing tests"

printf "</testsuites>\n" >> $DIR/tests.xml
