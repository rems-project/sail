import os
import re
import sys
import subprocess
import datetime

class color:
    NOTICE = '\033[94m'
    PASS = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    END = '\033[0m'


def step(string):
    p = subprocess.Popen(string, shell=True, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    out, err = p.communicate()
    status = p.wait()
    if status != 0:
        print("{}Failed{}: {}".format(color.FAIL, color.END, string))
        print('{}stdout{}:'.format(color.NOTICE, color.END))
        print(out)
        print('{}stderr{}:'.format(color.NOTICE, color.END))
        print(err)
        sys.exit(1)

def banner(string):
    print '-' * len(string)
    print string
    print '-' * len(string)

def collect_results(name, tests):
    passes = 0
    failures = 0
    xml = ""

    for test in tests:
        _, status = os.waitpid(tests[test], 0)
        if status != 0:
            failures += 1
            xml += '    <testcase name="{}">\n      <error message="fail">fail</error>\n    </testcase>\n'.format(test)
        else:
            passes += 1
            xml += '    <testcase name="{}"/>\n'.format(test)

    print '{}{} passes and {} failures{}'.format(color.NOTICE, passes, failures, color.END)

    time = datetime.datetime.utcnow()
    suite = '  <testsuite name="{}" tests="{}" failures="{}" timestamp="{}">\n{}  </testsuite>\n'
    xml = suite.format(name, passes + failures, failures, time, xml)
    return xml
