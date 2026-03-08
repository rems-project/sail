import os
import sys
import subprocess
import datetime
import argparse
import signal
import html
from abc import ABC, abstractmethod


def signal_handler(sig, frame):
    sys.exit(0)


signal.signal(signal.SIGINT, signal_handler)

parser = argparse.ArgumentParser("run_tests.py")
parser.add_argument(
    "--hide-error-output", help="Hide error information.", action="store_true"
)
parser.add_argument("--compact", help="Compact output.", action="store_true")
parser.add_argument(
    "--targets", help="Targets to use (where supported).", action="append"
)
parser.add_argument(
    "--update-expected",
    help="Update the expected file (where supported)",
    action="store_true",
)
parser.add_argument(
    "--run-skips", help="Run tests that would otherwise be skipped", action="store_true"
)
parser.add_argument("--test", help="Run only specified test.", action="append")
parser.add_argument(
    "--lean-local-support-library",
    help="Use a local Lean support library",
    action="store",
)
parser.add_argument("--seq", help="Run sequentially", action="store_true")
args = parser.parse_args()


class color:
    NOTICE = "\033[94m"
    PASS = "\033[92m"
    WARNING = "\033[93m"
    FAIL = "\033[91m"
    END = "\033[0m"


def compact_char(code, char):
    print(f"{code}{char}{color.END}", end="")
    sys.stdout.flush()


# Compute parallelism once at startup so the message only prints once.
if args.seq:
    _parallel_count = 1
else:
    try:
        _parallel_count = int(os.environ["TEST_PAR"])
    except (KeyError, ValueError):
        print("Running 16 tests in parallel. Set TEST_PAR to configure")
        _parallel_count = 16


def parallel():
    return _parallel_count


def _make_chunks(predicate):
    """Return a chunker function that batches filenames satisfying predicate."""

    def chunker(filenames, cores):
        ys = []
        chunk = []
        for filename in filenames:
            if predicate(filename):
                chunk.append(filename)
            if len(chunk) >= cores:
                ys.append(list(chunk))
                chunk = []
        ys.append(list(chunk))
        return ys

    return chunker


def _sail_file(filename):
    basename = os.path.splitext(os.path.basename(filename))[0]
    return (filename.endswith(".sail") or filename.endswith(".sail_project")) and (
        not args.test or basename in args.test
    )


chunks = _make_chunks(_sail_file)
directory_chunks = _make_chunks(os.path.isdir)
project_chunks = _make_chunks(lambda f: f.endswith(".sail_project"))


def step_with_status(string, expected_status=0, cwd=None, name="", stderr_file=""):
    p = subprocess.run(string, shell=True, capture_output=True, text=True, cwd=cwd)
    if p.returncode != expected_status:
        if args.compact:
            compact_char(color.FAIL, "X")
        else:
            print(f"{color.FAIL}Failed{color.END}: {name} {string}")
        if not args.hide_error_output:
            print(f"{color.NOTICE}stdout{color.END}:")
            print(p.stdout)
            print(f"{color.NOTICE}stderr{color.END}:")
            print(p.stderr)
            if stderr_file:
                try:
                    with open(stderr_file) as f:
                        print(f"{color.NOTICE}stderr file{color.END}:")
                        print(f.read())
                except FileNotFoundError:
                    print(f"File {stderr_file} not found")
    return p.returncode


def step(string, expected_status=0, cwd=None, name="", stderr_file=""):
    if (
        step_with_status(
            string,
            expected_status=expected_status,
            cwd=cwd,
            name=name,
            stderr_file=stderr_file,
        )
        != expected_status
    ):
        sys.exit(1)


class Results:
    def __init__(self, name):
        self.passes = 0
        self.failures = 0
        self.xfails = 0
        self._xfail_reasons = {}
        self._xml_lines = []
        self.name = name

    def expect_failure(self, test, reason):
        self._xfail_reasons[test] = reason

    def _add_status(self, test, result, msg):
        qmsg = html.escape(msg)
        self._xml_lines.append(
            f'    <testcase name="{test}">\n'
            f'      <{result} message="{qmsg}">{qmsg}</{result}>\n'
            f"    </testcase>\n"
        )

    def _add_failure(self, test, msg):
        self.failures += 1
        self._add_status(test, "error", msg)

    def collect(self, tests):
        for test in tests:
            _, status = os.waitpid(tests[test], 0)
            if test in self._xfail_reasons:
                reason = self._xfail_reasons[test]
                if status == 0:
                    self._add_failure(test, f"XPASS: {reason}")
                else:
                    self.xfails += 1
                    self._add_status(test, "skipped", f"XFAIL: {reason}")
                continue
            if status != 0:
                self._add_failure(test, "fail")
            else:
                self.passes += 1
                self._xml_lines.append(f'    <testcase name="{test}"/>\n')
        sys.stdout.flush()

    def finish(self):
        xfail_msg = f" ({self.xfails} expected failures)" if self.xfails else ""
        if args.compact:
            print()
        print(
            f"{color.NOTICE}{self.passes} passes and {self.failures} failures{xfail_msg}{color.END}"
        )
        time = datetime.datetime.utcnow()
        inner_xml = "".join(self._xml_lines)
        return (
            f'  <testsuite name="{self.name}" tests="{self.passes + self.failures}" '
            f'failures="{self.failures}" timestamp="{time}">\n'
            f"{inner_xml}"
            f"  </testsuite>\n"
        )


class SailTest(ABC):
    """Base class for Sail test runners.

    Subclasses override run() to call self.run_tests() one or more times, then
    invoke MyTests().main() at the bottom of the script.
    """

    def __init__(self):
        self.sail = os.environ.get("SAIL", "sail")
        self.sail_dir = self._get_sail_dir()
        self._xml_parts = []
        print(f"Sail is {self.sail}")
        print(f"Sail dir is {self.sail_dir}")

    def _get_sail_dir(self):
        sail_dir = os.environ.get("SAIL_DIR")
        if sail_dir:
            return sail_dir
        try:
            p = subprocess.run([self.sail, "--dir"], capture_output=True, text=True)
        except Exception as e:
            print(
                f"{color.FAIL}Unable to get Sail library directory from opam{color.END}"
            )
            print(e)
            sys.exit(1)
        if p.returncode == 0:
            return p.stdout.strip()
        print(
            f"{color.FAIL}Unable to get Sail library directory from sail --dir{color.END}"
        )
        print(f"{color.NOTICE}stdout{color.END}:")
        print(p.stdout)
        print(f"{color.NOTICE}stderr{color.END}:")
        print(p.stderr)
        sys.exit(1)

    def get_targets(self, default_targets):
        return args.targets or default_targets

    def banner(self, string):
        print("-" * len(string))
        print(string)
        print("-" * len(string))
        sys.stdout.flush()

    def _print_ok(self, name):
        if args.compact:
            compact_char(color.PASS, ".")
        else:
            print(f'{(name + " ").ljust(40, ".")} {color.PASS}ok{color.END}')

    def _print_skip(self, name):
        if args.compact:
            compact_char(color.WARNING, "s")
        else:
            print(f'{(name + " ").ljust(40, ".")} {color.WARNING}skip{color.END}')

    def run_tests(
        self,
        name,
        filenames,
        fn,
        *,
        testdir,
        expected_failures=None,
        skip_set=None,
        skip_fn=None,
        chunks_fn=None,
    ):
        """Run a set of tests in parallel using fork/collect.

        fn(filename, basename) is called in each child process and should use
        step() for each command. The child's working directory is set to testdir
        before fn is called. The base class calls _print_ok() and sys.exit(0)
        after fn returns.

        testdir: absolute path; the working directory for each test child process.
                 Also used as the base for resolving relative filenames in chunks_fn.
        expected_failures: dict of {filename: reason} for known xfails
        skip_set: set of basenames to skip before forking
        skip_fn: callable(filename, basename) -> bool for complex skip logic
        chunks_fn: replacement for the default chunks() function
        """
        results = Results(name)
        if expected_failures:
            for test, reason in expected_failures.items():
                results.expect_failure(test, reason)
        # Temporarily chdir to testdir so that chunks_fn predicates like
        # os.path.isdir() resolve correctly against the test data directory.
        saved_cwd = os.getcwd()
        try:
            os.chdir(testdir)
            all_chunks = (chunks_fn or chunks)(filenames, parallel())
        finally:
            os.chdir(saved_cwd)
        for chunk in all_chunks:
            tests = {}
            for filename in chunk:
                basename = os.path.splitext(os.path.basename(filename))[0]
                if (skip_set and basename in skip_set) or (
                    skip_fn and skip_fn(filename, basename)
                ):
                    self._print_skip(filename)
                    continue
                tests[filename] = os.fork()
                if tests[filename] == 0:
                    os.chdir(testdir)
                    fn(filename, basename)
                    self._print_ok(filename)
                    sys.exit(0)
            results.collect(tests)
        self._xml_parts.append(results.finish())

    @abstractmethod
    def run(self):
        pass

    def main(self, xml_dir=None):
        self.run()
        xml = "<testsuites>\n" + "".join(self._xml_parts) + "</testsuites>\n"
        out = os.path.join(xml_dir, "tests.xml") if xml_dir else "tests.xml"
        with open(out, "w") as f:
            f.write(xml)
