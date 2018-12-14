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

def parallel():
    try:
        return int(os.environ['TEST_PAR'])
    except Exception, e:
        print("Running 4 tests in parallel. Set TEST_PAR to configure")
        return 4

def chunks(filenames, cores):
    ys = []
    chunk = []
    for filename in filenames:
        if re.match('.+\.sail', filename):
            chunk.append(filename)
        if len(chunk) >= cores:
            ys.append(list(chunk))
            chunk = []
    ys.append(list(chunk))
    return ys

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
    sys.stdout.flush()

class Results:
    def __init__(self, name):
        self.passes = 0
        self.failures = 0
        self.xml = ""
        self.name = name

    def collect(self, tests):
        for test in tests:
            _, status = os.waitpid(tests[test], 0)
            if status != 0:
                self.failures += 1
                self.xml += '    <testcase name="{}">\n      <error message="fail">fail</error>\n    </testcase>\n'.format(test)
            else:
                self.passes += 1
                self.xml += '    <testcase name="{}"/>\n'.format(test)
        sys.stdout.flush()

    def finish(self):
        print '{}{} passes and {} failures{}'.format(color.NOTICE, self.passes, self.failures, color.END)

        time = datetime.datetime.utcnow()
        suite = '  <testsuite name="{}" tests="{}" failures="{}" timestamp="{}">\n{}  </testsuite>\n'
        self.xml = suite.format(self.name, self.passes + self.failures, self.failures, time, self.xml)
        return self.xml
