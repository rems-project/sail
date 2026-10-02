import os
import re
import subprocess
import pytest
import shutil
from pathlib import Path
from typing import List, Optional


def _get_sail_dir() -> Path:
    from_env = os.environ.get("SAIL_DIR")
    if from_env is not None:
        return Path(from_env)
    return Path(__file__).absolute().parent.parent


def _get_sail() -> Path:
    sail_bin = shutil.which(os.environ.get("SAIL", "sail"))
    return sail_bin if sail_bin is not None else Path("sail")


def _have_valgrind() -> bool:
    try:
        subprocess.check_call(["valgrind", "--version"])
        return True
    except subprocess.CalledProcessError:
        return False


SAIL_DIR = _get_sail_dir()
SAIL = _get_sail()
HAVE_VALGRIND = _have_valgrind()


def find_sail_files() -> List[pytest.param]:
    return [
        pytest.param(test, id=test.name)
        for test in Path(__file__).parent.glob("*.sail")
    ]


def run_command(
    command: List[str],
    expected_status: int = 0,
    stderr_file: Optional[Path] = None,
    cwd: Optional[Path] = None,
) -> str:
    process = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd
    )
    if process.returncode != expected_status:
        pytest.fail(
            f"Command '{' '.join(command)}' failed with exit code {process.returncode}\nstdout:\n{process.stdout.decode()}\nstderr:\n{process.stderr.decode()}"
        )
    if stderr_file:
        with open(stderr_file, "wb") as f:
            f.write(process.stderr)
    return process.stdout.decode()


def _run_sail_c_test(
    sail_file: Path,
    tmp_path: Path,
    sail_opts: List[str],
    c_opts=None,
    valgrind: bool = False,
    compiler: str = "cc",
    actually_cpp: bool = False,
    expected_failures=None,
) -> None:
    if expected_failures is None:
        expected_failures = {}
    if c_opts is None:
        c_opts = []
    if sail_file.name in expected_failures:
        pytest.xfail(expected_failures[sail_file.name])
    sail_file_abs = sail_file.absolute()
    basename = sail_file.stem

    if actually_cpp:
        extension = "cpp"
    else:
        extension = "c"

    if not os.path.isfile(SAIL) or not os.access(SAIL, os.X_OK):
        pytest.fail(f"Sail binary not found or not executable at {SAIL}")

    # Run from the tests directory to avoid embedding an absolute path to the sail
    # file in the error output.
    run_command(
        [SAIL] + sail_opts + [sail_file.name, "-o", tmp_path / basename],
        cwd=sail_file_abs.parent,
    )

    lib_files = [str(f) for f in Path(SAIL_DIR, "lib").glob("*.c")]

    run_command(
        [compiler]
        + c_opts
        + [f"{basename}.{extension}"]
        + lib_files
        + ["-lgmp", "-I", f"{SAIL_DIR}/lib", "-o", f"{basename}.bin"],
        cwd=tmp_path,
    )

    # For files using a config file, copy the config file to the temporary directory.
    sail_content = sail_file.read_text()
    match = re.search(r'sail_config_set_file\("([^"]+)"\)', sail_content)
    if match:
        config_filename = match.group(1)
        config_file_path = sail_file.parent / config_filename
        assert config_file_path.exists()
        shutil.copy(config_file_path, tmp_path)

    with Path(tmp_path, f"{basename}.result").open("w") as f:
        process = subprocess.run(
            [f"./{basename}.bin"],
            stdout=f,
            stderr=subprocess.PIPE,
            cwd=tmp_path,
        )
    if process.returncode != (1 if basename.startswith("fail") else 0):
        pytest.fail(
            f"Command './{basename}.bin' failed with exit code {process.returncode}\n"
            f"stdout:\n"
            f"(see {tmp_path / basename}.result)\n"
            f"stderr:\n"
            f"{process.stderr.decode()}"
        )
    expect_file = os.path.join(os.path.dirname(sail_file_abs), basename + ".expect")
    run_command(["diff", f"{tmp_path / basename}.result", expect_file], cwd=tmp_path)

    err_expect_file = sail_file_abs.with_suffix(".err_expect")
    if err_expect_file.exists():
        with Path(tmp_path, f"{basename}.err_result").open("wb") as f:
            f.write(process.stderr)
        run_command(
            ["diff", f"{tmp_path / basename}.err_result", err_expect_file], cwd=tmp_path
        )

    if valgrind and HAVE_VALGRIND and not basename.startswith("fail"):
        run_command(
            [
                "valgrind",
                "--leak-check=full",
                "--track-origins=yes",
                "--errors-for-leak-kinds=all",
                "--error-exitcode=2",
                f"./{basename}.bin",
            ],
            expected_status=1 if basename.startswith("fail") else 0,
            cwd=tmp_path,
        )


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_unoptimized_c(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(sail_file, tmp_path, sail_opts=["-c", "--c-no-mangle"])


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_unoptimized_c_mangle(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(sail_file, tmp_path, sail_opts=["-c"])


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_optimized_c(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(
        sail_file, tmp_path, c_opts=["-O2"], sail_opts=["-c", "-O"], valgrind=True
    )


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_constant_folding(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(sail_file, tmp_path, sail_opts=["-c", "-Oconstant_fold"])


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_undefined_behavior_sanitised(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(
        sail_file,
        tmp_path,
        c_opts=["-O2", "-fsanitize=undefined"],
        sail_opts=["-c", "-O"],
    )


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_address_sanitised(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(
        sail_file,
        tmp_path,
        c_opts=["-O2", "-fsanitize=address", "-g"],
        sail_opts=["-c", "-O"],
    )


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_unoptimized_c_with_cpp_compiler(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(
        sail_file,
        tmp_path,
        c_opts=["-xc++"],
        sail_opts=["-c"],
        compiler="c++",
        expected_failures={
            "cabbrev.sail": "my_pair_in_c is declared in a namespace in C++",
            "xlen_val.sail": "assumes variables are still global",
            "abstract_sizeof_no_use.sail": "difficult to call model.sail_set_abstract_... in the right place",
            "abstract_type.sail": "difficult to call model.sail_set_abstract_... in the right place",
            "tl_let_flow_change.sail": "difficult to call model.sail_set_abstract_... in the right place",
        },
    )


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_optimized_c_with_cpp_compiler(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(
        sail_file,
        tmp_path,
        c_opts=["-xc++", "-O2"],
        sail_opts=["-c", "-O"],
        valgrind=True,
        compiler="c++",
        expected_failures={
            "cabbrev.sail": "my_pair_in_c is declared in a namespace in C++",
            "xlen_val.sail": "assumes variables are still global",
            "abstract_sizeof_no_use.sail": "difficult to call model.sail_set_abstract_... in the right place",
            "abstract_type.sail": "difficult to call model.sail_set_abstract_... in the right place",
            "tl_let_flow_change.sail": "difficult to call model.sail_set_abstract_... in the right place",
            "config_abstract_type2.sail": "Valgrind failure",
        },
    )


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_unoptimized_cpp(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(
        sail_file,
        tmp_path,
        sail_opts=["--cpp"],
        compiler="c++",
        actually_cpp=True,
        expected_failures={
            "cabbrev.sail": "my_pair_in_c is declared in a namespace in C++",
            "xlen_val.sail": "assumes variables are still global",
            "abstract_sizeof_no_use.sail": "difficult to call model.sail_set_abstract_... in the right place",
            "abstract_type.sail": "difficult to call model.sail_set_abstract_... in the right place",
            "tl_let_flow_change.sail": "difficult to call model.sail_set_abstract_... in the right place",
        },
    )


@pytest.mark.parametrize("sail_file", find_sail_files())
def test_optimized_cpp(sail_file: Path, tmp_path: Path) -> None:
    _run_sail_c_test(
        sail_file,
        tmp_path,
        c_opts=["-O2"],
        sail_opts=["--cpp", "-O"],
        valgrind=True,
        compiler="c++",
        actually_cpp=True,
        expected_failures={
            "cabbrev.sail": "my_pair_in_c is declared in a namespace in C++",
            "xlen_val.sail": "assumes variables are still global",
            "abstract_sizeof_no_use.sail": "difficult to call model.sail_set_abstract_... in the right place",
            "abstract_type.sail": "difficult to call model.sail_set_abstract_... in the right place",
            "tl_let_flow_change.sail": "difficult to call model.sail_set_abstract_... in the right place",
        },
    )
