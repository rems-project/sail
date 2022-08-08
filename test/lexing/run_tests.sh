#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAIL=${SAIL:=sail}

rm -f $DIR/tests.xml

printf "\$SAIL is $SAIL\n"

# shellcheck source=../test_helpers.sh
source "$DIR/../test_helpers.sh"

printf "<testsuites>\n" >> $DIR/tests.xml

for file in $DIR/*.sail;
do
    pushd $DIR > /dev/null;
    if $SAIL $(basename $file) 2> $DIR/result 1> /dev/null;
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

exit $returncode
