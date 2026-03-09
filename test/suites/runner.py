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
    required="--list-suites" not in sys.argv,
)
sailtest.parser.add_argument(
    "--list-suites",
    help="Print available test suites as a tree and exit",
    action="store_true",
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


def _matches_prefix(registered_name, requested_name):
    """Return True if requested_name is a dot-segment prefix of registered_name."""
    registered_parts = registered_name.split(".")
    requested_parts = requested_name.split(".")
    return registered_parts[: len(requested_parts)] == requested_parts


def _build_tree(names):
    tree = {}
    for name in sorted(names):
        node = tree
        for part in name.split("."):
            node = node.setdefault(part, {})
    return tree


def _print_tree(tree, prefix=""):
    items = sorted(tree.items())
    for i, (key, subtree) in enumerate(items):
        is_last = i == len(items) - 1
        if prefix:
            connector = "└── " if is_last else "├── "
            print(f"{prefix}{connector}{key}")
            child_prefix = prefix + ("  " if is_last else "│ ")
        else:
            print(key)
            child_prefix = "  "
        _print_tree(subtree, child_prefix)


# Import all suite modules by file path so they register themselves via @suite(...).
# File-based loading avoids shadowing Python built-in module names (e.g. builtins).
_suites_dir = os.path.dirname(os.path.abspath(__file__))
for _path in glob.glob(os.path.join(_suites_dir, "*.py")):
    _name = os.path.splitext(os.path.basename(_path))[0]
    if _name not in ("sailtest", "runner"):
        _spec = importlib.util.spec_from_file_location(_name, _path)
        _module = importlib.util.module_from_spec(_spec)
        _spec.loader.exec_module(_module)

if sailtest.args.list_suites:
    _print_tree(_build_tree(sailtest._suite_registry))
    sys.exit(0)

for suite_name in sailtest.args.suite:
    matches = [
        (name, cls, xml_dir)
        for name, (cls, xml_dir) in sailtest._suite_registry.items()
        if _matches_prefix(name, suite_name)
    ]
    if not matches:
        print(f"Unknown suite: {suite_name}")
        print(f"Available suites: {', '.join(sorted(sailtest._suite_registry))}")
        sys.exit(1)
    for name, cls, xml_dir in matches:
        cls().main(xml_dir=xml_dir, name=name)
