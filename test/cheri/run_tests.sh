#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR
SAILDIR="$DIR/../.."

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

rm -f $DIR/tests.xml

# shellcheck source=../test_helpers.sh
source "$SAILDIR/test/test_helpers.sh"

SAILLIBDIR="$DIR/../../lib/"

printf "<testsuites>\n" >> $DIR/tests.xml

printf "Building MIPS specification...\n"

if make -C $SAILDIR/mips mips ;
then
    green "Building MIPS specification" "ok"
else
    red "Building MIPS specification" "fail"
fi

printf "Building MIPS_C specification...\n"

if make -C $SAILDIR/mips mips_c ;
then
    green "Building MIPS_C specification" "ok"
else
    red "Building MIPS_C specification" "fail"
fi

printf "Booting FreeBSD-MIPS...\n"

bunzip2 -fk freebsd-beri-sim-mdroot-smoketest_bootonly-kernel.bz2
time $SAILDIR/mips/mips_c --cyclelimit 85000000 --binary 0x100000,freebsd-beri-sim-mdroot-smoketest_bootonly-kernel --binary 0x7f010000,sim.dtb  --image simboot_128m.sailbin > freebsd_out.txt
if  grep -q 'Done booting' freebsd_out.txt;
then
    green "Booting FreeBSD MIPS" "ok"
else
    red "Booting FreeBSD MIPS" "fail"
fi

printf "Building CHERI 256 specification...\n"

if make -C $SAILDIR/cheri cheri ;
then
    green "Building CHERI 256 specification" "ok"
else
    red "Building CHERI 256 specification" "fail"
fi

printf "Building CHERI 128 specification...\n"

if make -C $SAILDIR/cheri cheri128 ;
then
    green "Building CHERI 128 specification" "ok"
else
    red "Building CHERI 128 specification" "fail"
fi

finish_suite "CHERI tests"

printf "</testsuites>\n" >> $DIR/tests.xml

