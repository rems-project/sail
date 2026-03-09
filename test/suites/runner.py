#!/usr/bin/env python3

import importlib
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

for suite in sailtest.args.suite:
    module = importlib.import_module(suite)
    for obj in vars(module).values():
        if (
            isinstance(obj, type)
            and issubclass(obj, sailtest.SailTest)
            and obj is not sailtest.SailTest
        ):
            obj().main(xml_dir=module._SUITE_DIR)
            break
