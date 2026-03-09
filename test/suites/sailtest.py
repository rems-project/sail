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

TEST_DIR = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

parser = argparse.ArgumentParser()
# args and parallelism are set by runner.py after argument parsing.
args = None
parallelism = None

_suite_registry = {}


def suite(name, xml_dir):
    """Decorator that registers a SailTest subclass under the given name."""

    def decorator(cls):
        _suite_registry[name] = (cls, xml_dir)
        return cls

    return decorator


class Color:
    NOTICE = "\033[94m"
    PASS = "\033[92m"
    WARNING = "\033[93m"
    FAIL = "\033[91m"
    END = "\033[0m"


def compact_char(code, char):
    print(f"{code}{char}{Color.END}", end="")
    sys.stdout.flush()


def sail_file(filename):
    basename = os.path.splitext(os.path.basename(filename))[0]
    return (filename.endswith(".sail") or filename.endswith(".sail_project")) and (
        not args.test or basename in args.test
    )


class Batcher:
    """Encapsulates a directory and a predicate for batching its entries into parallel chunks."""

    def __init__(self, directory, predicate=None):
        self.directory = directory
        self._predicate = predicate if predicate is not None else sail_file

    @classmethod
    def directories(cls, directory):
        """Batcher that matches subdirectories."""
        return cls(directory, predicate=os.path.isdir)

    @classmethod
    def projects(cls, directory):
        """Batcher that matches .sail_project files."""
        return cls(directory, predicate=lambda f: f.endswith(".sail_project"))

    def batch(self, parallelism):
        """List the directory, filter by predicate, and split into batches of at most `parallelism` items."""
        batches = []
        batch = []
        for filename in os.listdir(self.directory):
            if self._predicate(os.path.join(self.directory, filename)):
                batch.append(filename)
            if len(batch) >= parallelism:
                batches.append(list(batch))
                batch = []
        if batch:
            batches.append(list(batch))
        return batches


def step_with_status(string, expected_status=0, cwd=None, name="", stderr_file="", env=None):
    merged_env = {**os.environ, **env} if env else None
    p = subprocess.run(string, shell=True, capture_output=True, text=True, cwd=cwd, env=merged_env)
    if p.returncode != expected_status:
        if args.compact:
            compact_char(Color.FAIL, "X")
        else:
            print(f"{Color.FAIL}Failed{Color.END}: {name} {string}")
        if not args.hide_error_output:
            print(f"{Color.NOTICE}stdout{Color.END}:")
            print(p.stdout)
            print(f"{Color.NOTICE}stderr{Color.END}:")
            print(p.stderr)
            if stderr_file:
                try:
                    with open(stderr_file) as f:
                        print(f"{Color.NOTICE}stderr file{Color.END}:")
                        print(f.read())
                except FileNotFoundError:
                    print(f"File {stderr_file} not found")
    return p.returncode


def step(string, expected_status=0, cwd=None, name="", stderr_file="", env=None):
    if (
        step_with_status(
            string,
            expected_status=expected_status,
            cwd=cwd,
            name=name,
            stderr_file=stderr_file,
            env=env,
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
            f"{Color.NOTICE}{self.passes} passes and {self.failures} failures{xfail_msg}{Color.END}"
        )
        time = datetime.datetime.now(datetime.timezone.utc)
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
                f"{Color.FAIL}Unable to get Sail library directory from opam{Color.END}"
            )
            print(e)
            sys.exit(1)
        if p.returncode == 0:
            return p.stdout.strip()
        print(
            f"{Color.FAIL}Unable to get Sail library directory from sail --dir{Color.END}"
        )
        print(f"{Color.NOTICE}stdout{Color.END}:")
        print(p.stdout)
        print(f"{Color.NOTICE}stderr{Color.END}:")
        print(p.stderr)
        sys.exit(1)

    def banner(self, string):
        print("-" * len(string))
        print(string)
        print("-" * len(string))
        sys.stdout.flush()

    def _print_ok(self, name):
        if args.compact:
            compact_char(Color.PASS, ".")
        else:
            print(f'{(name + " ").ljust(40, ".")} {Color.PASS}ok{Color.END}')

    def _print_skip(self, name):
        if args.compact:
            compact_char(Color.WARNING, "s")
        else:
            print(f'{(name + " ").ljust(40, ".")} {Color.WARNING}skip{Color.END}')

    def run_tests(
        self,
        name,
        batcher,
        fn,
        *,
        testdir,
        expected_failures=None,
        skip_set=None,
        skip_fn=None,
    ):
        """Run a set of tests in parallel using fork/collect.

        fn(filename, basename) is called in each child process and should use
        step() for each command. The child's working directory is set to testdir
        before fn is called. The base class calls _print_ok() and sys.exit(0)
        after fn returns.

        batcher: a Batcher instance that provides the files to test and how to
                 batch them. Its directory is listed and filtered by its predicate.
        testdir: absolute path; the working directory for each test child process.
        expected_failures: dict of {filename: reason} for known xfails
        skip_set: set of basenames to skip before forking
        skip_fn: callable(filename, basename) -> bool for complex skip logic
        """
        results = Results(name)
        if expected_failures:
            for test, reason in expected_failures.items():
                results.expect_failure(test, reason)
        batches = batcher.batch(parallelism)
        for batch in batches:
            tests = {}
            for filename in batch:
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

    def main(self, xml_dir=None, name="tests"):
        self.run()
        xml = "<testsuites>\n" + "".join(self._xml_parts) + "</testsuites>\n"
        out = os.path.join(xml_dir, f"{name}.xml") if xml_dir else f"{name}.xml"
        with open(out, "w") as f:
            f.write(xml)
