#!/usr/bin/env python3

# Tests for every extern (primitive) declared in the Sail library.
#
# Each primitive in src/lib/externs.json has a test file <name>.sail
# here (with any '#' in the name replaced by '_hash'), containing a
# main function that exercises it. A test passes if main runs to
# completion without an assertion failure or other error. If a test
# prints anything, its expected standard output and standard error go
# in <name>.expect and <name>.err_expect respectively (both default to
# empty). Running with --update-expected rewrites these files from the
# actual output of each test that runs to completion, other than those
# listed as expected failures below. Files named <name>_inc.sail test
# the variants used with `default Order inc`.

import os
import sys
import json
import subprocess

mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.join(mydir, '..'))

from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()
targets = get_targets(['interpreter'])

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))
print("Targets: {}".format(targets))

externs_json = os.path.join('..', '..', 'src', 'lib', 'externs.json')

def test_name(extern):
    return extern.replace('#', '_hash')

# Primitives that the interpreter does not (yet) support, and why.
interpreter_xfails = {}

def read_file(filename, default=''):
    try:
        with open(filename, 'r') as file:
            return file.read()
    except FileNotFoundError:
        return default

def fail(basename, message):
    try:
        with open(report_path(os.getpid()), 'a') as file:
            file.write(message + '\n')
    except OSError:
        pass
    if is_compact():
        compact_char(color.FAIL, 'X')
    else:
        print('{}Failed{}: {}'.format(color.FAIL, color.END, basename))
        if not args.hide_error_output:
            print(message)
    sys.exit(1)

def check_output(basename, stream, expected_file, actual):
    expected = read_file(expected_file)
    if actual == expected:
        return
    # Never update the expected output of a test we expect to fail, as
    # that would record the incorrect behaviour as correct.
    if args.update_expected and basename not in interpreter_xfails:
        print('Updating {}'.format(expected_file))
        if actual:
            with open(expected_file, 'w') as file:
                file.write(actual)
        else:
            # A missing file means the output should be empty
            os.remove(expected_file)
        return
    fail(basename, 'Unexpected {}\nexpected:\n{}\nactual:\n{}'.format(stream, expected, actual))

def test_coverage():
    banner('Checking every extern has a test, and every test an extern')
    results = Results('coverage')
    with open(externs_json, 'r') as file:
        externs = json.load(file)['externs']
    names = sorted(set(extern['name'] for extern in externs))
    tests = set(test_name(name) for name in names)
    problems = []

    def problem(test, message):
        problems.append(message)
        results._add_failure(test, message)

    for name in names:
        if not os.path.exists(test_name(name) + '.sail'):
            problem(name, 'No test file {}.sail for extern {}'.format(test_name(name), name))
        else:
            results.passes += 1

    # Tests (and their expected output) for externs that no longer exist
    for filename in sorted(os.listdir('.')):
        basename, ext = os.path.splitext(filename)
        if ext == '.sail':
            if basename in tests or (basename.endswith('_inc') and basename[:-len('_inc')] in tests):
                continue
            problem(filename, 'Test {} does not correspond to any extern'.format(filename))
        elif ext in ['.expect', '.err_expect'] and not os.path.exists(basename + '.sail'):
            problem(filename, 'Expected output {} has no test file {}.sail'.format(filename, basename))

    for test in sorted(interpreter_xfails):
        if not os.path.exists(test + '.sail'):
            problem(test, 'Expected failure listed for {}, which has no test file {}.sail'.format(test, test))

    for message in problems:
        print('{}Failed{}: {}'.format(color.FAIL, color.END, message))
    return results.finish()

def test_interpreter(name):
    banner('Testing {}'.format(name))
    results = Results(name)
    for test, reason in interpreter_xfails.items():
        results.expect_failure(test + '.sail', reason)
    for filenames in chunks(sorted(os.listdir('.')), parallel()):
        # Anything left in the buffer would be printed again by each child
        sys.stdout.flush()
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            tests[filename] = os.fork()
            if tests[filename] == 0:
                iresult = '_{}.iresult'.format(basename)
                cmd = [sail, '--no-warn', '-is', 'run.isail', '-iout', iresult, filename]
                try:
                    p = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
                except subprocess.TimeoutExpired:
                    fail(basename, 'Timed out: {}'.format(' '.join(cmd)))
                stdout = read_file(iresult)
                if os.path.exists(iresult):
                    os.remove(iresult)
                if p.returncode != 0:
                    fail(basename, 'Command failed: {}\nExited with status {}\nstdout:\n{}\nstderr:\n{}'
                         .format(' '.join(cmd), p.returncode, p.stdout, p.stderr))
                # The interpreter reports runtime errors (including failed
                # assertions) but still exits successfully, so check the
                # result of running main.
                log = p.stdout.splitlines()
                if 'main()' not in log or log[log.index('main()') + 1:] != ['Result = ()']:
                    fail(basename, 'main did not complete successfully:\n{}'.format(p.stdout))
                check_output(basename, 'stdout', basename + '.expect', stdout)
                check_output(basename, 'stderr', basename + '.err_expect', p.stderr)
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()

xml = '<testsuites>\n'

xml += test_coverage()

if 'interpreter' in targets:
    if sys.platform.startswith('win32') or sys.platform.startswith('cygwin'):
        print('Skipping interpreter tests because the interpreter is only supported on Unix-like platforms')
    else:
        xml += test_interpreter('interpreter')

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()
