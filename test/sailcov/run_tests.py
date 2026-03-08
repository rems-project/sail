#!/usr/bin/env python3

import os
import sys

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

class SailcovTests(SailTest):
    def run(self):
        sailcov = '{}/sailcov/sailcov'.format(self.sail_dir)
        banner('Testing sailcov')
        if not self._have_sailcov(sailcov):
            print('Skipping because no sailcov executable found')
            # Append an empty suite so tests.xml is still written
            self._xml_parts.append(Results('sailcov').finish())
            return
        self.run_tests('sailcov', os.listdir('.'), self._make_test(sailcov))

    def _have_sailcov(self, sailcov):
        try:
            subprocess.call([sailcov, '--help'], stdout=subprocess.DEVNULL)
            return True
        except FileNotFoundError:
            return False

    def _make_test(self, sailcov):
        def fn(filename, basename):
            step('\'{}\' -no_warn -no_memo_z3 -c -c_include sail_coverage.h -c_coverage {}.branches {} -o {}'.format(
                self.sail, basename, filename, basename))
            step('cc {}.c \'{}\'/lib/*.c \'{}\'/lib/coverage/target/release/libsail_coverage.a -lgmp -lpthread -ldl -I \'{}\'/lib -o {}.bin'.format(
                basename, self.sail_dir, self.sail_dir, self.sail_dir, basename))
            step('./{}.bin -c {}.taken'.format(basename, basename))
            step('\'{}\' --werror --all {}.branches --taken {}.taken {}'.format(
                sailcov, basename, basename, filename))
            step('diff {}.html {}.expect'.format(basename, basename))
            step('rm {}.taken {}.bin {}.branches'.format(basename, basename, basename))
        return fn

SailcovTests().main()
