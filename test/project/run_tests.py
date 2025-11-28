#!/usr/bin/env python3

import os
import re
import sys
import hashlib

os.environ["SAIL_NEW_CLI"] = "true"

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_project():
    banner('Testing project')
    results = Results('project')
    for filenames in chunks(os.listdir('failure'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('\'{}\' failure/{} 2> failure/{}.error'.format(sail, filename, basename), expected_status = 1)
                step('diff failure/{}.expect failure/{}.error'.format(basename, basename))
                step('rm failure/{}.error'.format(basename))
                print_ok(filename)
                sys.exit(0)
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_project()

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
