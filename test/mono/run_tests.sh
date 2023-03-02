#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR=${SAIL_DIR:-"$DIR/../.."}
SAIL=${SAIL:=sail}
TESTSDIR="$DIR"
OUTPUTDIR="$DIR/test-output"

rm -f $DIR/tests.xml

printf "\$SAIL is $SAIL\n"

# shellcheck source=../test_helpers.sh
source "$SAILDIR/test/test_helpers.sh"

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
    if "$SAIL" -lem -lem_mwords -lem_lib Test_extra -o out $(< "$i_full") &>>log;
    then
        mv out.lem out_types.lem "$OUTPUTDIR"
	if lem -ocaml -lib "$SAILDIR/src/lem_interp" \
               -outdir "$OUTPUTDIR" \
               "$SAILDIR/src/gen_lib/sail2_values.lem" \
               "$SAILDIR/src/gen_lib/sail2_operators.lem" \
               "$SAILDIR/src/gen_lib/sail2_operators_mwords.lem" \
               "$SAILDIR/src/gen_lib/sail2_instr_kinds.lem" \
               "$SAILDIR/src/gen_lib/sail2_prompt.lem" \
               "$SAILDIR/src/gen_lib/sail2_state_monad.lem" \
               "$SAILDIR/src/gen_lib/sail2_state.lem" \
               "$SAILDIR/src/gen_lib/sail2_prompt_monad.lem" \
               "$SAILDIR/src/gen_lib/sail2_string.lem" \
               "$SAILDIR/src/gen_lib/sail2_undefined.lem" \
               "$DIR/test_extra.lem" \
               "$OUTPUTDIR/out_types.lem" "$OUTPUTDIR/out.lem" &>>log;
	then
            cd "$OUTPUTDIR"
            if grep -q initial_regstate out.lem; then TESTML=../test_with_state.ml; else TESTML=../test.ml; fi
            if ocamlfind ocamlc -linkpkg -package zarith -package lem \
                         sail2_values.ml sail2_operators.ml \
                         sail2_instr_kinds.ml sail2_prompt_monad.ml sail2_prompt.ml \
                         sail2_operators_mwords.ml sail2_state_monad.ml sail2_state.ml \
                         sail2_string.ml sail2_undefined.ml \
                         test_extra.ml out_types.ml out.ml $TESTML \
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
