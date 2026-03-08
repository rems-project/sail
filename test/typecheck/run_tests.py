#!/usr/bin/env python3

import os
import re
import sys
from shutil import which

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.realpath('..'))

from sailtest import *

class TypecheckTests(SailTest):
    def run(self):
        step('mkdir -p rtpass')
        step('mkdir -p rtpass2')

        skip_pass = set()
        if which('cvc4') is None:
            skip_pass.add('type_pow_zero')

        banner('Testing passing programs')
        self.run_tests('pass', os.listdir('pass'), self._test_pass, skip_set=skip_pass)

        banner('Testing multi-file projects')
        self.run_tests('projects', os.listdir('project'), self._test_project, chunks_fn=project_chunks)

        banner('Testing failing programs')
        self.run_tests('fail', os.listdir('fail'), self._test_fail)

    def _test_pass(self, filename, basename):
        step('\'{}\' --no-memo-z3 --just-check --strict-bitvector --ddump-tc-ast pass/{} 1> rtpass/{}'.format(
            self.sail, filename, filename))
        step('\'{}\' --no-memo-z3 --just-check --strict-bitvector --ddump-tc-ast --dallow-internal rtpass/{} 1> rtpass2/{}'.format(
            self.sail, filename, filename))
        step('diff rtpass/{} rtpass2/{}'.format(filename, filename))
        variantdir = os.path.join('pass', basename)
        for variantname in os.listdir(variantdir) if os.path.isdir(variantdir) else []:
            if re.match('.+\\.sail$', variantname):
                variantbasename = os.path.splitext(os.path.basename(variantname))[0]
                step('\'{}\' --no-memo-z3 --strict-bitvector pass/{}/{} 2> pass/{}/{}.error'.format(
                    self.sail, basename, variantname, basename, variantbasename), expected_status=1)
                step('diff pass/{}/{}.error pass/{}/{}.expect'.format(
                    basename, variantbasename, basename, variantbasename))
                step('rm pass/{}/{}.error'.format(basename, variantbasename))

    def _test_project(self, filename, basename):
        if filename.startswith('fail'):
            step('\'{}\' --no-memo-z3 --strict-bitvector project/{} --all-modules 2> project/{}.error'.format(
                self.sail, filename, basename), expected_status=1)
            step('diff project/{}.error project/{}.expect'.format(basename, basename))
            step('rm project/{}.error'.format(basename))
        else:
            step('\'{}\' --no-memo-z3 project/{} --all-modules'.format(self.sail, filename))

    def _test_fail(self, filename, basename):
        step('\'{}\' --no-memo-z3 --strict-bitvector fail/{} 2> fail/{}.error'.format(
            self.sail, filename, basename), expected_status=1)
        step('diff fail/{}.error fail/{}.expect'.format(basename, basename))
        step('rm fail/{}.error'.format(basename))

TypecheckTests().main()
