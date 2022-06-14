#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAIL=${SAIL:=sail}
printf "\$SAIL is $SAIL\n"

for i in `ls $DIR/pass/ | grep '\.isail$'`;
do
    source=`echo $i | sed -e 's/^\(.*[^0-9]\)[0-9]*\.isail$/\1.sail/'`
    expected=`basename -s .isail $i`.expected
    echo $i
    "$SAIL" $DIR/pass/$source -is $DIR/pass/$i
    grep -v '^overload\|\$include' out.sail > $DIR/pass/$expected
    rm out.sail
done
