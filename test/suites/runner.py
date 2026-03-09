#!/usr/bin/env python3

import glob
import importlib
import importlib.util
import os
import sys

import sailtest

sailtest.parser.add_argument(
    "-s",
    "--suite",
    help="Test suite to run (may be passed multiple times)",
    action="append",
    required=True,
)

sailtest.args = sailtest.parser.parse_args()

if sailtest.args.parallelism is not None:
    sailtest.parallelism = sailtest.args.parallelism
else:
    try:
        sailtest.parallelism = int(os.environ["TEST_PAR"])
    except (KeyError, ValueError):
        print("Running 16 tests in parallel. Set TEST_PAR to configure")
        sailtest.parallelism = 16

# Import all suite modules by file path so they register themselves via @suite(...).
# File-based loading avoids shadowing Python built-in module names (e.g. builtins).
_suites_dir = os.path.dirname(os.path.abspath(__file__))
for _path in glob.glob(os.path.join(_suites_dir, "*.py")):
    _name = os.path.splitext(os.path.basename(_path))[0]
    if _name not in ("sailtest", "runner"):
        _spec = importlib.util.spec_from_file_location(_name, _path)
        _module = importlib.util.module_from_spec(_spec)
        _spec.loader.exec_module(_module)

for suite_name in sailtest.args.suite:
    if suite_name not in sailtest._suite_registry:
        print(f"Unknown suite: {suite_name}")
        print(f"Available suites: {', '.join(sorted(sailtest._suite_registry))}")
        sys.exit(1)
    cls, xml_dir = sailtest._suite_registry[suite_name]
    cls().main(xml_dir=xml_dir)
