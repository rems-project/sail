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

def signal_handler(sig, frame):
    sys.exit(0)

signal.signal(signal.SIGINT, signal_handler)

parser = argparse.ArgumentParser("run_tests.py")
parser.add_argument("--hide-error-output", help="Hide error information.", action='store_true')
parser.add_argument("--compact", help="Compact output.", action='store_true')
parser.add_argument("--targets", help="Targets to use (where supported).", action='append')
parser.add_argument("--update-expected", help="Update the expected file (where supported)", action="store_true")
parser.add_argument("--run-skips", help="Run tests that would otherwise be skipped", action="store_true")
parser.add_argument("--test", help="Run only specified test.", action='append')
parser.add_argument("--lean-local-support-library", help="Use a local Lean support library", action='store')
parser.add_argument("--seq", help="Run sequentially", action='store_true')
args = parser.parse_args()

def is_compact():
    return args.compact

def get_targets(default_targets):
    if args.targets is None:
        return default_targets
    else:
        return args.targets

def compact_char(code, char):
    print('{}{}{}'.format(code, char, color.END), end='')
    sys.stdout.flush()

class color:
    NOTICE = '\033[94m'
    PASS = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    END = '\033[0m'

def get_sail_dir():
    try:
        return os.environ['SAIL_DIR']
    except KeyError:
        try:
            p = subprocess.run([get_sail(), "--dir"], capture_output=True, text=True)
        except Exception as e:
            print('{}Unable to get Sail library directory from opam{}'.format(color.FAIL, color.END))
            print(e)
            sys.exit(1)

        if p.returncode == 0:
            return p.stdout.strip()
        else:
            print('{}Unable to get Sail library directory from sail --dir{}'.format(color.FAIL, color.END))
            print('{}stdout{}:'.format(color.NOTICE, color.END))
            print(p.stdout)
            print('{}stderr{}:'.format(color.NOTICE, color.END))
            print(p.stderr)
            sys.exit(1)

def print_ok(name):
    if is_compact():
        compact_char(color.PASS, '.')
    else:
        print('{} {}{}{}'.format('{} '.format(name).ljust(40, '.'), color.PASS, 'ok', color.END))

def print_skip(name):
    if is_compact():
        compact_char(color.WARNING, 's')
    else:
        print('{} {}{}{}'.format('{} '.format(name).ljust(40, '.'), color.WARNING, 'skip', color.END))

def get_sail():
    try:
        return os.environ['SAIL']
    except KeyError:
        return 'sail'

def parallel():
    if args.seq:
        return 1
    try:
        return int(os.environ['TEST_PAR'])
    except Exception as e:
        print("Running 16 tests in parallel. Set TEST_PAR to configure")
        return 16

def chunks(filenames, cores):
    ys = []
    chunk = []
    for filename in filenames:
        basename = os.path.splitext(os.path.basename(filename))[0]
        if (re.match(r'.+\.sail$', filename) or re.match(r'.+\.sail_project$', filename)) and (not args.test or basename in args.test):
            chunk.append(filename)
        if len(chunk) >= cores:
            ys.append(list(chunk))
            chunk = []
    ys.append(list(chunk))
    return ys

def directory_chunks(filenames, cores):
    ys = []
    chunk = []
    for filename in filenames:
        if os.path.isdir(filename):
            chunk.append(filename)
        if len(chunk) >= cores:
            ys.append(list(chunk))
            chunk = []
    ys.append(list(chunk))
    return ys

def project_chunks(filenames, cores):
    ys = []
    chunk = []
    for filename in filenames:
        if re.match(r'.+\.sail_project$', filename):
            chunk.append(filename)
        if len(chunk) >= cores:
            ys.append(list(chunk))
            chunk = []
    ys.append(list(chunk))
    return ys

# Most test suites run each test in a forked child process, so the parent only
# ever sees the child's exit status. To get something more useful than 'fail'
# into the JUnit XML (and hence into the GitHub CI output), a failing child
# leaves a description of what went wrong in this directory, in a file named
# after its pid, which the parent picks up when it reaps the child.
report_dir = tempfile.mkdtemp(prefix='sail-test-reports-')
report_dir_owner = os.getpid()

def cleanup_report_dir():
    # Forked children run atexit handlers too, and must not delete the reports
    # belonging to their siblings, so only the creating process cleans up.
    if os.getpid() == report_dir_owner:
        shutil.rmtree(report_dir, ignore_errors=True)

atexit.register(cleanup_report_dir)

def report_path(pid):
    return os.path.join(report_dir, str(pid))

def take_report(pid):
    """Read and remove the failure report left behind by a child process."""
    try:
        with open(report_path(pid), 'r') as file:
            report = file.read()
        os.remove(report_path(pid))
    except OSError:
        return ''
    return report.strip()

# How much of each captured stream to keep in the report. The full output is
# always in the test log; this is just what gets embedded in the XML.
max_captured_output = 4000

def truncate_output(string):
    string = string.strip()
    if len(string) > max_captured_output:
        return string[:max_captured_output] + '\n[... truncated, see the full test log]'
    return string

def record_failure(command, status, expected_status, out, err, stderr_file, file_content):
    lines = ['Command failed: {}'.format(command),
             'Exited with status {} (expected {})'.format(status, expected_status)]
    for header, content in [('stdout', out), ('stderr', err), (stderr_file, file_content)]:
        content = truncate_output(content)
        if content:
            lines.append('{}:\n{}'.format(header, content))
    try:
        with open(report_path(os.getpid()), 'a') as file:
            file.write('\n'.join(lines) + '\n')
    except OSError:
        # A missing report just means a less informative message
        pass

def describe_status(status):
    if os.WIFSIGNALED(status):
        return 'was killed by signal {}'.format(os.WTERMSIG(status))
    if os.WIFEXITED(status):
        return 'exited with status {}'.format(os.WEXITSTATUS(status))
    return 'returned wait status {}'.format(status)

ansi_escape = re.compile(r'\x1b\[[0-9;]*[a-zA-Z]')
invalid_xml_char = re.compile(r'[^\x09\x0a\x0d\x20-\uD7FF\uE000-\uFFFD]')

def xml_text(msg):
    # Test output is full of terminal colour codes, and can contain other
    # control characters that XML cannot represent at all.
    return invalid_xml_char.sub('', ansi_escape.sub('', msg))

def step_with_status(string, expected_status=0, cwd=None, name='', stderr_file=''):
    p = subprocess.Popen(string, shell=True, stderr=subprocess.PIPE, stdout=subprocess.PIPE, cwd=cwd)
    out, err = p.communicate()
    status = p.wait()
    if status != expected_status:
        out = out.decode('utf-8', errors='replace')
        err = err.decode('utf-8', errors='replace')
        file_content = ''
        if stderr_file != '':
            try:
                with open(stderr_file, 'r') as file:
                    file_content = file.read()
            except FileNotFoundError:
                file_content = 'File {} not found'.format(stderr_file)
        record_failure(string, status, expected_status, out, err, stderr_file, file_content)
        if is_compact():
            compact_char(color.FAIL, 'X')
        else:
            print("{}Failed{}: {} {}".format(color.FAIL, color.END, name, string))
        if not args.hide_error_output:
            print('{}stdout{}:'.format(color.NOTICE, color.END))
            print(out)
            print('{}stderr{}:'.format(color.NOTICE, color.END))
            print(err)
            if stderr_file != '':
                print('{}stderr file{}:'.format(color.NOTICE, color.END))
                print(file_content)
    return status

def step(string, expected_status=0, cwd=None, name='', stderr_file=''):
    if step_with_status(string, expected_status=expected_status, cwd=cwd, name=name, stderr_file=stderr_file) != expected_status:
        sys.exit(1)

def banner(string):
    print('-' * len(string))
    print(string)
    print('-' * len(string))
    sys.stdout.flush()

class Results:
    def __init__(self, name):
        self.passes = 0
        self.failures = 0
        self.xfails = 0
        self._xfail_reasons = {}
        self.xml = ""
        self.name = name
        self._start = datetime.datetime.now()

    def expect_failure(self, test, reason):
        self._xfail_reasons[test] = reason

    def _add_status(self, test, result, msg):
        # The message attribute is what CI tends to show first, so it gets the
        # summary line, and the full details go in the element body.
        msg = xml_text(msg)
        summary = html.escape(msg.split('\n')[0])
        details = html.escape(msg)
        test = html.escape(test)
        suite = html.escape(self.name)
        self.xml += f'    <testcase name="{test}" classname="{suite}">\n      <{result} message="{summary}">{details}</{result}>\n    </testcase>\n'

    def _add_failure(self, test, msg):
        self.failures += 1
        self._add_status(test, "failure", msg)

    def collect(self, tests):
        for test in tests:
            pid = tests[test]
            _, status = os.waitpid(pid, 0)
            report = take_report(pid)
            if test in self._xfail_reasons:
                reason = self._xfail_reasons[test]
                if status == 0:
                    self._add_failure(test, "XPASS: " + reason)
                else:
                    self.xfails += 1
                    self._add_status(test, "skipped", "XFAIL: " + reason)
                continue
            if status != 0:
                summary = '{} {}'.format(test, describe_status(status))
                self._add_failure(test, (summary + '\n\n' + report) if report else summary)
            else:
                self.passes += 1
                self.xml += '    <testcase name="{}" classname="{}"/>\n'.format(html.escape(test), html.escape(self.name))
        sys.stdout.flush()

    def finish(self):
        xfail_msg = f' ({self.xfails} expected failures)' if self.xfails else ''
        if is_compact():
            print()
        print('{}{} passes and {} failures{}{}'.format(color.NOTICE, self.passes, self.failures, xfail_msg, color.END))

        timestamp = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
        duration = (datetime.datetime.now() - self._start).total_seconds()
        tests = self.passes + self.failures + self.xfails
        suite = '  <testsuite name="{}" tests="{}" failures="{}" errors="0" skipped="{}" time="{:.3f}" timestamp="{}">\n{}  </testsuite>\n'
        self.xml = suite.format(html.escape(self.name), tests, self.failures, self.xfails, duration, timestamp, self.xml)
        return self.xml
