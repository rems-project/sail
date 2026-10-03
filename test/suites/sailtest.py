import os
import re
import sys
import subprocess
import datetime
import argparse
import signal
import html
import atexit
import shutil
import tempfile
from abc import ABC, abstractmethod


def signal_handler(sig, frame):
    sys.exit(0)


signal.signal(signal.SIGINT, signal_handler)

TEST_DIR = os.path.normpath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
)

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
        for filename in sorted(os.listdir(self.directory)):
            if self._predicate(os.path.join(self.directory, filename)):
                batch.append(filename)
            if len(batch) >= parallelism:
                batches.append(list(batch))
                batch = []
        if batch:
            batches.append(list(batch))
        return batches


# Each test runs in a forked child process, so the parent only ever sees the
# child's exit status. To get something more useful than 'fail' into the JUnit
# XML (and hence into the GitHub CI output), a failing child leaves a
# description of what went wrong in this directory, in a file named after its
# pid, which the parent picks up when it reaps the child.
report_dir = tempfile.mkdtemp(prefix="sail-test-reports-")
report_dir_owner = os.getpid()


def cleanup_report_dir():
    # Forked children run atexit handlers too, and must not delete the reports
    # belonging to their siblings, so only the creating process cleans up.
    if os.getpid() == report_dir_owner:
        shutil.rmtree(report_dir, ignore_errors=True)


atexit.register(cleanup_report_dir)


def report_path(pid):
    return os.path.join(report_dir, str(pid))


def report(message):
    """Add a message to the failure report for the current (child) process."""
    try:
        with open(report_path(os.getpid()), "a") as f:
            f.write(message.rstrip("\n") + "\n")
    except OSError:
        # A missing report just means a less informative message
        pass


def take_report(pid):
    """Read and remove the failure report left behind by a child process."""
    try:
        with open(report_path(pid)) as f:
            contents = f.read()
        os.remove(report_path(pid))
    except OSError:
        return ""
    return contents.strip()


# How much of each captured stream to keep in the report. The full output is
# always in the test log; this is just what gets embedded in the XML.
max_captured_output = 4000


def truncate_output(string):
    string = string.strip()
    if len(string) > max_captured_output:
        return string[:max_captured_output] + "\n[... truncated, see the full test log]"
    return string


def record_failure(
    command, status, expected_status, out, err, stderr_file, file_content
):
    lines = [
        f"Command failed: {command}",
        f"Exited with status {status} (expected {expected_status})",
    ]
    for header, content in [
        ("stdout", out),
        ("stderr", err),
        (stderr_file, file_content),
    ]:
        content = truncate_output(content)
        if content:
            lines.append(f"{header}:\n{content}")
    report("\n".join(lines))


def describe_status(status):
    if os.WIFSIGNALED(status):
        return f"was killed by signal {os.WTERMSIG(status)}"
    if os.WIFEXITED(status):
        return f"exited with status {os.WEXITSTATUS(status)}"
    return f"returned wait status {status}"


ansi_escape = re.compile(r"\x1b\[[0-9;]*[a-zA-Z]")
invalid_xml_char = re.compile(r"[^\x09\x0a\x0d\x20-퟿-�]")


def xml_text(msg):
    # Test output is full of terminal colour codes, and can contain other
    # control characters that XML cannot represent at all.
    return invalid_xml_char.sub("", ansi_escape.sub("", msg))


def step_with_status(
    string, expected_status=0, cwd=None, name="", stderr_file="", env=None
):
    merged_env = {**os.environ, **env} if env else None
    p = subprocess.run(
        string,
        shell=True,
        capture_output=True,
        text=True,
        errors="replace",
        cwd=cwd,
        env=merged_env,
    )
    if p.returncode != expected_status:
        file_content = ""
        if stderr_file:
            try:
                with open(stderr_file) as f:
                    file_content = f.read()
            except FileNotFoundError:
                file_content = f"File {stderr_file} not found"
        record_failure(
            string,
            p.returncode,
            expected_status,
            p.stdout,
            p.stderr,
            stderr_file,
            file_content,
        )
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
                print(f"{Color.NOTICE}stderr file{Color.END}:")
                print(file_content)
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
        self._start = datetime.datetime.now()

    def expect_failure(self, test, reason):
        self._xfail_reasons[test] = reason

    def _add_status(self, test, result, msg):
        # The message attribute is what CI tends to show first, so it gets the
        # summary line, and the full details go in the element body.
        msg = xml_text(msg)
        summary = html.escape(msg.split("\n")[0])
        details = html.escape(msg)
        self._xml_lines.append(
            f'    <testcase name="{html.escape(test)}" classname="{html.escape(self.name)}">\n'
            f'      <{result} message="{summary}">{details}</{result}>\n'
            f"    </testcase>\n"
        )

    def add_pass(self, test):
        self.passes += 1
        self._xml_lines.append(
            f'    <testcase name="{html.escape(test)}" classname="{html.escape(self.name)}"/>\n'
        )

    def add_failure(self, test, msg):
        self.failures += 1
        self._add_status(test, "failure", msg)

    def add_skip(self, test, msg):
        self._add_status(test, "skipped", msg)

    def collect(self, tests):
        for test in tests:
            pid = tests[test]
            _, status = os.waitpid(pid, 0)
            child_report = take_report(pid)
            if test in self._xfail_reasons:
                reason = self._xfail_reasons[test]
                if status == 0:
                    self.add_failure(test, f"XPASS: {reason}")
                else:
                    self.xfails += 1
                    self.add_skip(test, f"XFAIL: {reason}")
                continue
            if status != 0:
                summary = f"{test} {describe_status(status)}"
                self.add_failure(
                    test, f"{summary}\n\n{child_report}" if child_report else summary
                )
            else:
                self.add_pass(test)
        sys.stdout.flush()

    def finish(self):
        xfail_msg = f" ({self.xfails} expected failures)" if self.xfails else ""
        if args.compact:
            print()
        print(
            f"{Color.NOTICE}{self.passes} passes and {self.failures} failures{xfail_msg}{Color.END}"
        )
        timestamp = datetime.datetime.now(datetime.timezone.utc).isoformat(
            timespec="seconds"
        )
        duration = (datetime.datetime.now() - self._start).total_seconds()
        tests = self.passes + self.failures + self.xfails
        inner_xml = "".join(self._xml_lines)
        return (
            f'  <testsuite name="{html.escape(self.name)}" tests="{tests}" '
            f'failures="{self.failures}" errors="0" skipped="{self.xfails}" '
            f'time="{duration:.3f}" timestamp="{timestamp}">\n'
            f"{inner_xml}"
            f"  </testsuite>\n"
        )


class SailTest(ABC):
    """Base class for Sail test runners.

    Subclasses override run() to call self.run_tests() one or more times, and
    are registered with the @suite decorator so runner.py can find them.
    """

    # If set, test failures in this suite make runner.py exit with a non-zero
    # status. Otherwise failures are only reported in the output and XML.
    fail_on_error = False

    def __init__(self):
        self.sail = os.environ.get("SAIL", "sail")
        self.sail_dir = self._get_sail_dir()
        self._xml_parts = []
        self.failures = 0
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
            # Otherwise a child forked after this would print it again
            sys.stdout.flush()

    def add_results(self, results):
        """Finish a Results object and include it in this suite's XML output."""
        self.failures += results.failures
        self._xml_parts.append(results.finish())

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
        # The test directory may only hold generated files, and so not exist in
        # a fresh checkout (e.g. test/lem).
        os.makedirs(testdir, exist_ok=True)
        batches = batcher.batch(parallelism)
        for batch in batches:
            # Anything left in the buffer would be printed again by each child
            sys.stdout.flush()
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
        self.add_results(results)

    @abstractmethod
    def run(self):
        pass

    def main(self, xml_dir=None, name="tests"):
        """Run the suite and write its XML. Returns the number of failures."""
        self.run()
        xml = "<testsuites>\n" + "".join(self._xml_parts) + "</testsuites>\n"
        if xml_dir:
            os.makedirs(xml_dir, exist_ok=True)
        out = os.path.join(xml_dir, f"{name}.xml") if xml_dir else f"{name}.xml"
        with open(out, "w") as f:
            f.write(xml)
        return self.failures
