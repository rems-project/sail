#!/usr/bin/env python3

import os
import re
import sys
import hashlib

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test():
    banner('Testing')
    results = Results("one-off")
    for dirs in directory_chunks(os.listdir('.'), parallel()):
        tests = {}
        for dir in dirs:
            tests[dir] = os.fork()
            if tests[dir] == 0:
                os.chdir(dir)
                step('./test.sh')
                print_ok(dir)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test()

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
