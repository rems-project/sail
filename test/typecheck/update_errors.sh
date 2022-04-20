#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAIL=${SAIL:=sail}

for i in `ls $DIR/pass/ | grep sail`;
do
    shopt -s nullglob;
    for file in $DIR/pass/${i%.sail}/*.sail;
    do
        pushd $DIR/pass > /dev/null;
        $SAIL -no_memo_z3 ${i%.sail}/$(basename $file) 2> ${file%.sail}.expect || true;
        popd > /dev/null
    done
done

for file in $DIR/fail/*.sail;
do
    pushd $DIR/fail > /dev/null;
    $SAIL -no_memo_z3 $(basename $file) 2> ${file%.sail}.expect || true;
    popd > /dev/null
done
