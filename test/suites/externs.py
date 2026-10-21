# Tests for every extern (primitive) declared in the Sail library.
#
# Each primitive in src/lib/externs.json has a test file <name>.sail
# in test/externs (with any '#' in the name replaced by '_hash'),
# containing a main function that exercises it. A test passes if main
# runs to completion without an assertion failure or other error. If a
# test prints anything, its expected standard output and standard
# error go in <name>.expect and <name>.err_expect respectively (both
# default to empty). Running with --update-expected rewrites these
# files from the actual output of each test that runs to completion,
# other than those listed as expected failures below. Files named
# <name>_inc.sail test the variants used with `default Order inc`.

import os
import sys
import json

from sailtest import *

_SUITE_DIR = os.path.join(TEST_DIR, "externs")
_EXTERNS_JSON = os.path.join(TEST_DIR, "..", "src", "lib", "externs.json")


def test_name(extern):
    return extern.replace("#", "_hash")


# Primitives that the interpreter does not (yet) support, and why.
interpreter_xfails = {}


def read_file(filename, default=""):
    try:
        with open(filename) as f:
            return f.read()
    except FileNotFoundError:
        return default


def fail(basename, message):
    report(message)
    if args.compact:
        compact_char(Color.FAIL, "X")
    else:
        print(f"{Color.FAIL}Failed{Color.END}: {basename}")
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
        print(f"Updating {expected_file}")
        if actual:
            with open(expected_file, "w") as f:
                f.write(actual)
        else:
            # A missing file means the output should be empty
            os.remove(expected_file)
        return
    fail(basename, f"Unexpected {stream}\nexpected:\n{expected}\nactual:\n{actual}")


@suite("externs.coverage", _SUITE_DIR)
class ExternsCoverageTests(SailTest):
    def run(self):
        self.banner("Checking every extern has a test, and every test an extern")
        results = Results("coverage")
        with open(_EXTERNS_JSON) as f:
            externs = json.load(f)["externs"]
        names = sorted(set(extern["name"] for extern in externs))
        tests = set(test_name(name) for name in names)
        problems = []

        def problem(test, message):
            problems.append(message)
            results.add_failure(test, message)

        def exists(filename):
            return os.path.exists(os.path.join(_SUITE_DIR, filename))

        for name in names:
            if not exists(f"{test_name(name)}.sail"):
                problem(name, f"No test file {test_name(name)}.sail for extern {name}")
            else:
                results.passes += 1

        # Tests (and their expected output) for externs that no longer exist
        for filename in sorted(os.listdir(_SUITE_DIR)):
            basename, ext = os.path.splitext(filename)
            if ext == ".sail":
                if basename in tests or (
                    basename.endswith("_inc") and basename[: -len("_inc")] in tests
                ):
                    continue
                problem(filename, f"Test {filename} does not correspond to any extern")
            elif ext in [".expect", ".err_expect"] and not exists(f"{basename}.sail"):
                problem(
                    filename,
                    f"Expected output {filename} has no test file {basename}.sail",
                )

        for test in sorted(interpreter_xfails):
            if not exists(f"{test}.sail"):
                problem(
                    test,
                    f"Expected failure listed for {test}, which has no test file {test}.sail",
                )

        for message in problems:
            print(f"{Color.FAIL}Failed{Color.END}: {message}")
        self.add_results(results)


@suite("externs.interpreter", _SUITE_DIR)
class ExternsInterpreterTests(SailTest):
    def run(self):
        if sys.platform.startswith("win32") or sys.platform.startswith("cygwin"):
            print(
                "Skipping interpreter tests because the interpreter is only supported on Unix-like platforms"
            )
            return
        self.banner("Testing interpreter")
        self.run_tests(
            "interpreter",
            Batcher(_SUITE_DIR),
            self._test,
            testdir=_SUITE_DIR,
            expected_failures={
                f"{test}.sail": reason for test, reason in interpreter_xfails.items()
            },
        )

    def _test(self, filename, basename):
        iresult = f"_{basename}.iresult"
        cmd = [self.sail, "--no-warn", "-is", "run.isail", "-iout", iresult, filename]
        try:
            p = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            fail(basename, f"Timed out: {' '.join(cmd)}")
        stdout = read_file(iresult)
        if os.path.exists(iresult):
            os.remove(iresult)
        if p.returncode != 0:
            fail(
                basename,
                f"Command failed: {' '.join(cmd)}\nExited with status {p.returncode}\n"
                f"stdout:\n{p.stdout}\nstderr:\n{p.stderr}",
            )
        # The interpreter reports runtime errors (including failed
        # assertions) but still exits successfully, so check the
        # result of running main.
        log = p.stdout.splitlines()
        if "main()" not in log or log[log.index("main()") + 1 :] != ["Result = ()"]:
            fail(basename, f"main did not complete successfully:\n{p.stdout}")
        check_output(basename, "stdout", f"{basename}.expect", stdout)
        check_output(basename, "stderr", f"{basename}.err_expect", p.stderr)
