RED='\033[0;91m'
GREEN='\033[0;92m'
YELLOW='\033[0;93m'
NC='\033[0m'

pass=0
fail=0
returncode=0
XML=""

function green {
    (( pass += 1 ))
    printf "%s: ${GREEN}$2${NC}\n" "$1"
    XML+="    <testcase name=\"$1\"/>\n"
}

function yellow {
    (( fail += 1 ))
    returncode=1
    printf "%s: ${YELLOW}$2${NC}\n" "$1"
    XML+="    <testcase name=\"$1\">\n      <error message=\"$2\">$2</error>\n    </testcase>\n"
}

function red {
    (( fail += 1 ))
    returncode=1
    printf "%s: ${RED}$2${NC}\n" "$1"
    XML+="    <testcase name=\"$1\">\n      <error message=\"$2\">$2</error>\n    </testcase>\n"
}

function finish_suite {
    printf "%s: Passed ${pass} out of $(( pass + fail ))\n\n" "$1"
    XML="  <testsuite name=\"$1\" tests=\"$(( pass + fail ))\" failures=\"${fail}\" timestamp=\"$(date)\">\n$XML  </testsuite>\n"
    # Note: we use echo -e to escape \n characters
    echo -e "$XML" >> "$DIR/tests.xml"
    XML=""
    pass=0
    fail=0
}
