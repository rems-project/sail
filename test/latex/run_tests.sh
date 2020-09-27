#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR"
SAILDIR="$DIR/../.."

rm -f "$DIR/tests.xml"

# shellcheck source=../test_helpers.sh
source "$SAILDIR/test/test_helpers.sh"


printf "<testsuites>\n" >> "$DIR/tests.xml"

find . -name '*.sail' -print0 | while IFS= read -r -d '' line; do 
    echo "$line"
done

for testfile in *.sail; do
    temp_dir=$(mktemp -d)
    trap 'rm -rf $temp_dir' 0 2 3 15
    
    if (cd "$temp_dir" && "$SAILDIR/sail" -o "out" -latex "$DIR/$testfile"); then
        # compare with expected files
        exp_prefix=${testfile//.sail/}
        errmsg="Missing .exp files for $testfile?"
        for expected in "${exp_prefix}"*.exp; do
            echo "expected=$expected"
            # remove prefix and suffix
            exp_file_name=${expected//${exp_prefix}./}
            generated_file="$temp_dir/out/${exp_file_name//.exp/}"
            if [ ! -f "$generated_file" ]; then
                errmsg="missing expected output $generated_file"
                break;
            elif ! diff -q "$generated_file" "$expected"; then
                diff -u "$generated_file" "$expected" || true
                errmsg="output is different"
                break
            else
                errmsg=""
            fi
        done
        if [ -z "$errmsg" ]; then
            green "LaTeX for $testfile" "ok"
        else
            yellow "LaTeX for $testfile" "$errmsg"
        fi;
    else
        red "failed to generate latex for $testfile" "fail"
    fi
    rm -rf "$temp_dir"
done

finish_suite "LaTeX testing"

printf "</testsuites>\n" >> "$DIR/tests.xml"
