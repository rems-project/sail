#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."
TESTSDIR="$DIR"
OUTPUTDIR="$DIR/test-output"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

rm -f $DIR/tests.xml

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
    printf "$1: Passed ${pass} out of $(( pass + fail ))\n\n"
    XML="  <testsuite name=\"$1\" tests=\"$(( pass + fail ))\" failures=\"${fail}\" timestamp=\"$(date)\">\n$XML  </testsuite>\n"
    printf "$XML" >> "$DIR/tests.xml"
    XML=""
    pass=0
    fail=0
}

printf "<testsuites>\n" >> "$DIR/tests.xml"

cd "$DIR"
mkdir -p "$OUTPUTDIR"

echo > log

if [ -z "$1" ]
then
    TESTS=`find $TESTSDIR/pass -type f | sort`
else
    TESTS="$@"
fi

for i_full in $TESTS;
do
    cd "$DIR"
    i=`basename "$i_full"`
    echo "Running test $i" >> log
    if "$SAILDIR/sail" -lem -lem_mwords -lem_lib Test_extra -o out $(< "$i_full") &>>log;
    then
        mv out.lem out_types.lem "$OUTPUTDIR"
	if lem -ocaml -lib "$SAILDIR/src/lem_interp" \
               -outdir "$OUTPUTDIR" \
               "$SAILDIR/src/gen_lib/sail2_values.lem" \
               "$SAILDIR/src/gen_lib/sail2_operators.lem" \
               "$SAILDIR/src/gen_lib/sail2_operators_mwords.lem" \
               "$SAILDIR/src/lem_interp/sail2_instr_kinds.lem" \
               "$SAILDIR/src/gen_lib/sail2_prompt.lem" \
               "$SAILDIR/src/gen_lib/sail2_state_monad.lem" \
               "$SAILDIR/src/gen_lib/sail2_state.lem" \
               "$SAILDIR/src/gen_lib/sail2_prompt_monad.lem" \
               "$SAILDIR/src/gen_lib/sail2_string.lem" \
               "$DIR/test_extra.lem" \
               "$OUTPUTDIR/out_types.lem" "$OUTPUTDIR/out.lem" &>>log;
	then
            cd "$OUTPUTDIR"
            if ocamlfind ocamlc -linkpkg -package zarith -package lem \
                         sail2_values.ml sail2_operators.ml \
                         sail2_instr_kinds.ml sail2_prompt_monad.ml sail2_prompt.ml \
                         sail2_operators_mwords.ml sail2_state_monad.ml sail2_state.ml \
                         sail2_string.ml \
                         test_extra.ml out_types.ml out.ml ../test.ml \
                         -o test &>>"$DIR/log"
            then
                if ./test &>>"$DIR/log"
                then
	            green "tested $i expecting pass" "pass"
                else
	            red "tested $i expecting pass" "running generated test failed"
                fi
            else
	        red "tested $i expecting pass" "compiling generated OCaml failed"
            fi
	else
	    red "tested $i expecting pass" "failed to generate OCaml from Lem"
	fi
    else
	red "tested $i expecting pass" "failed to generate Lem"
    fi
    echo >> "$DIR/log"
done

finish_suite "monomorphisation tests"

printf "</testsuites>\n" >> $DIR/tests.xml
