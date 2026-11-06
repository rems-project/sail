#!/usr/bin/env python3
"""Check single/split module output and public imports with a module-enabled runtime.

Run with --sail PATH --support-library PATH --toolchain leanprover/lean4:VERSION.
The support library must provide Lean modules (rems-project/lean-sail#13).
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile


def run(command, cwd, env, build=False):
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    if build and "Build completed successfully" not in result.stdout:
        raise RuntimeError("Lake exited without a successful-build marker")


def normalize(source):
    """Only module visibility may differ between the two generator modes."""
    lines = []
    for line in source.splitlines():
        line = line.strip()
        if not line or line in {"module", "@[expose] public section"}:
            continue
        if line.startswith("public import ") or line.startswith("public meta import "):
            line = line.removeprefix("public ")
        lines.append(line)
    return lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sail", required=True, type=Path)
    parser.add_argument("--plugin", type=Path, help="Lean plugin for an uninstalled compiler")
    parser.add_argument("--support-library", required=True, type=Path)
    parser.add_argument("--toolchain", required=True)
    args = parser.parse_args()
    sail = args.sail.resolve()
    runtime = args.support_library.resolve()
    if "module" not in (runtime / "Sail.lean").read_text().splitlines():
        parser.error("--support-library must provide Lean module-system files")
    env = dict(os.environ, ELAN_TOOLCHAIN=args.toolchain)
    lake = ["elan", "run", args.toolchain, "lake"]
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=runtime, text=True).strip()
    fixtures = {
        "leaf.sail": "function leaf(x : bool) -> bool = x\n",
        "model.sail": '$include "leaf.sail"\nfunction use_leaf(x : bool) -> bool = leaf(x)\n',
        "Supplement.lean": "  import Sail\nimport THE_MODULE_NAME.Defs\n"
            "namespace THE_MODULE_NAME\ndef supplement : Nat := 7\nend THE_MODULE_NAME\n",
        "NoImports.lean": "namespace THE_MODULE_NAME\ndef noImports : Nat := 11\nend THE_MODULE_NAME\n",
        "AlreadyModule.lean": "module\npublic import Sail\n@[expose] public section\n"
            "namespace THE_MODULE_NAME\ndef alreadyModule : Nat := 13\nend THE_MODULE_NAME\n",
    }
    with tempfile.TemporaryDirectory(prefix="sail-lean-modules-") as directory:
        root = Path(directory)
        for name, content in fixtures.items():
            (root / name).write_text(content)
        for single in [False, True]:
            outputs = []
            for modules in [False, True]:
                destination = root / f"{'single' if single else 'split'}-{'module' if modules else 'legacy'}"
                destination.mkdir()
                command = [str(sail)]
                if args.plugin:
                    command += ["--plugin", str(args.plugin.resolve())]
                command += ["model.sail", "--lean", "-o", "model",
                           "--lean-output-dir", str(destination),
                           "--lean-lib-repo", runtime.as_uri(), "--lean-lib-rev", revision]
                for fixture in ["Supplement", "NoImports", "AlreadyModule"]:
                    command += ["--lean-import-file", str(root / f"{fixture}.lean")]
                if single:
                    command.append("--lean-single-file")
                if modules:
                    command.append("--lean-module-system")
                run(command, root, env)
                project = destination / "model"
                outputs.append(project)
                sources = sorted(project.rglob("*.lean"))
                if modules:
                    for source in sources:
                        text = source.read_text()
                        if text.splitlines().count("module") != 1:
                            raise AssertionError(f"Expected exactly one module header: {source}")
                        if "@[expose] public section" not in text:
                            raise AssertionError(f"Missing public definitions: {source}")
                copied = project / "Model/AlreadyModule.lean"
                if copied.read_text() != fixtures["AlreadyModule.lean"].replace("THE_MODULE_NAME", "Model"):
                    raise AssertionError("Explicit module visibility was changed")
                run(lake + ["update", "Sail"], project, env)
                run(lake + ["--no-cache", "build", "--wfail", "--iofail"], project, env, build=True)
                run(["git", "init", "-q"], project, env)
                run(["git", "add", "."], project, env)
                run(["git", "-c", "user.name=Sail test", "-c", "user.email=sail-test@example.invalid",
                     "commit", "-qm", "Generated consumer fixture"], project, env)
                generated_revision = subprocess.check_output(
                    ["git", "rev-parse", "HEAD"], cwd=project, text=True).strip()
                consumer = destination / "consumer"
                consumer.mkdir()
                (consumer / "lean-toolchain").write_text(args.toolchain + "\n")
                (consumer / "lakefile.toml").write_text(
                    'name = "consumer"\ndefaultTargets = ["Consumer"]\n'
                    '[[lean_lib]]\nname = "Consumer"\n'
                    '[[require]]\nname = "model"\n'
                    f'git = {json.dumps(project.as_uri())}\nrev = "{generated_revision}"\n')
                (consumer / "Consumer.lean").write_text(
                    'import Model\n'
                    'example : Model.Functions.use_leaf true = true := rfl\n'
                    'example : Model.supplement = 7 := rfl\n'
                    'example : Model.noImports = 11 := rfl\n'
                    'example : Model.alreadyModule = 13 := rfl\n')
                run(lake + ["update", "model"], consumer, env)
                run(lake + ["--no-cache", "build", "--wfail", "--iofail"], consumer, env, build=True)
            legacy, modules = outputs
            for source in sorted(legacy.glob("**/*.lean")):
                relative = source.relative_to(legacy)
                if ".lake" in relative.parts:
                    continue
                if normalize(source.read_text()) != normalize((modules / relative).read_text()):
                    raise AssertionError(f"Generator modes changed more than visibility: {relative}")
    print("Single/split module output and ordinary external consumers passed.")


if __name__ == "__main__":
    main()
