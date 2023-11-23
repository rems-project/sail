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
