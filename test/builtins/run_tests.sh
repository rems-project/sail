
#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
SAILDIR="$DIR/../.."
LEMBUILDDIR="$DIR/_lembuild"

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
    printf "$XML" >> $DIR/tests.xml
    XML=""
    pass=0
    fail=0
}

printf "<testsuites>\n" >> $DIR/tests.xml

shopt -s nullglob;
for file in $DIR/*.sail;
do
    if $SAILDIR/sail -no_warn -c -O $file 1> ${file%.sail}.c 2> /dev/null;
    then
	green "compiling $(basename $file) (C)" "ok";
	if gcc -I $SAILDIR/lib/ ${file%.sail}.c -lgmp;
	then
	    green "compiling $(basename ${file%.sail}.c)" "ok";
	    if $DIR/a.out;
	    then
		green "tested $(basename ${file%.sail}) (C)" "ok"
	    else
		red "tested $(basename ${file%.sail}) (C)" "fail"
	    fi
	else
	    red "compiling $file" "fail"
	fi
    else
	red "compiling $file" "fail"
    fi;

    # if $SAILDIR/sail -no_warn -o out -ocaml $file 1> /dev/null 2> /dev/null;
    # then
    # 	green "compiling $(basename $file) (OCaml)" "ok"
    # 	if $DIR/out;
    # 	then
    # 	    green "tested $(basename ${file%.sail}) (OCaml)" "ok"
    # 	else
    # 	    red "tested $(basename ${file%.sail}) (OCaml)" "fail"
    # 	fi
    # else
    # 	red "compiling $(basename $file) (OCaml)" "fail"
    # fi;

    # mkdir -p "$LEMBUILDDIR"

    # if "$SAILDIR/sail" -no_warn -lem -lem_mwords -lem_lib Test_extras -undefined_gen -o out "$file" 1> /dev/null 2> /dev/null;
    # then
    #     mv out.lem out_types.lem "$LEMBUILDDIR"
    #     if lem -ocaml -lib "$SAILDIR/src/lem_interp" \
    #            -outdir "$LEMBUILDDIR" \
    #            "$SAILDIR/src/gen_lib/sail_values.lem" \
    #            "$SAILDIR/src/gen_lib/sail_operators.lem" \
    #            "$SAILDIR/src/gen_lib/sail_operators_mwords.lem" \
    #            "$SAILDIR/src/lem_interp/sail_instr_kinds.lem" \
    #            "$SAILDIR/src/gen_lib/prompt.lem" \
    #            "$SAILDIR/src/gen_lib/state_monad.lem" \
    #            "$SAILDIR/src/gen_lib/state.lem" \
    #            "$SAILDIR/src/gen_lib/prompt_monad.lem" \
    #            "test_extras.lem" "$LEMBUILDDIR/out_types.lem" "$LEMBUILDDIR/out.lem" 1> /dev/null 2> /dev/null;
    #     then
    #         cd "$LEMBUILDDIR"
    #         if ocamlfind ocamlc -linkpkg -package zarith -package lem \
    #                      sail_values.ml sail_operators.ml \
    #                      sail_instr_kinds.ml prompt_monad.ml prompt.ml \
    #                      sail_operators_mwords.ml state_monad.ml state.ml \
    #                      test_extras.ml out_types.ml out.ml ../test.ml \
    #                      -o test 1> /dev/null 2> /dev/null
    #         then
    #             green "compiling $(basename $file) (Lem)" "ok"
    #             if ./test 1> /dev/null 2> /dev/null
    #             then
    # 	            green "tested $(basename ${file%.sail}) (Lem)" "ok"
    #             else
    # 	            red "tested $(basename ${file%.sail}) (Lem)" "fail"
    #             fi
    #         else
    #             red "compiling $(basename $file) (Sail->Lem->Ocaml->Bytecode)" "fail"
    #         fi
    #         cd "$DIR"
    #     else
    #         red "compiling $(basename $file) (Sail->Lem->Ocaml)" "fail"
    #     fi
    # else
    #     red "compiling $(basename $file) (Sail->Lem)" "fail"
    # fi;

    rm -rf $DIR/_sbuild/;
    rm -rf "$LEMBUILDDIR";
    rm -f Out_lemmas.thy;
    rm -f out_types.lem;
    rm -f out.lem;
    rm -f ${file%.sail}.c;
    rm -f a.out;
    rm -f out
done

finish_suite "builtin testing"

printf "</testsuites>\n" >> $DIR/tests.xml
