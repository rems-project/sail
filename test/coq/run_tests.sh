#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."
SAIL=${SAIL:=sail}
TYPECHECKTESTSDIR="$DIR/../typecheck/pass"
EXTRATESTSDIR="$DIR/pass"

printf "\$SAIL is $SAIL\n"

if opam config var coq-sail:share >/dev/null 2>/dev/null; then
  COQOPTS=""
else
  if [ -z "$COQSAIL" ]; then
    COQSAIL="$DIR/../../../coq-sail/src"
  fi
  COQOPTS="-Q $COQSAIL Sail"
fi

if opam config var coq-bbv:share >/dev/null 2>/dev/null; then
  :
else
  if [ -z "$BBVDIR" ]; then
    BBVDIR="$DIR/../../../bbv/src/bbv"
  fi
  COQOPTS+=" -Q $BBVDIR bbv"
fi

printf "Coq options are: $COQOPTS\n"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

rm -f $DIR/tests.xml

# shellcheck source=../test_helpers.sh
source "$SAILDIR/test/test_helpers.sh"

printf "<testsuites>\n" >> $DIR/tests.xml

cd $DIR

function check_tests_dir {
    TESTSDIR="$1"
    for i in `ls $TESTSDIR/ | grep sail | grep -vf "$DIR/skip"`;
    do
        if $SAIL -coq -dcoq_undef_axioms -o out $TESTSDIR/$i &>/dev/null;
        then
    	if coqc $COQOPTS out_types.v &>/dev/null &&
    	   coqc $COQOPTS out.v &>/dev/null;
    	then
    	    green "tested $i expecting pass" "pass"
    	else
    	    yellow "tested $i expecting pass" "failed to typecheck generated Coq"
    	fi
        else
    	red "tested $i expecting pass" "failed to generate Coq"
        fi
    done
}

check_tests_dir "$TYPECHECKTESTSDIR"
check_tests_dir "$EXTRATESTSDIR"

finish_suite "Coq tests"

printf "</testsuites>\n" >> $DIR/tests.xml
