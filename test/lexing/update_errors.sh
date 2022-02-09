#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SAILDIR="$DIR/../.."

for file in $DIR/*.sail;
do
    printf "Updating $(basename $file)\n";
    $SAILDIR/sail $(basename $file) 2> ${file%.sail}.expect || true
done
