# Unit tests

Unit tests for the public `libsail` interface, written with
[Alcotest](https://github.com/mirage/alcotest). They exercise the
library the same way an external consumer would through the public
`Libsail` module interfaces.

## Running

```
SAIL_UNIT_TESTS=true dune runtest test/unit
```

The `SAIL_UNIT_TESTS` environment variable gates the tests: without
it, a plain `dune build` (and `make sail`) does not compile these
tests, so Alcotest is not required for the normal build. The tests are
part of the main dune project, so they link the in-tree `libsail` and
test working-tree changes and not an installed copy.

To run a single test group or case, pass Alcotest's filter arguments
after `--`:

```
SAIL_UNIT_TESTS=true dune exec test/unit/test_libsail.exe -- test Sail_file.utf16_to_byte
```

## Layout

- `test_libsail.ml` — the runner. It collects the `suites` from each
  per-file module and passes them to `Alcotest.run`.
- `test_<file>.ml` — one module per Libsail file under test (e.g.
  `test_sail_file.ml` for `Sail_file`), each exposing
  `val suites : unit Alcotest.test list`.

To test a new Libsail file, add a `test_<file>.ml` module exposing a
`suites` value and append `Test_<file>.suites` to the list in
`test_libsail.ml`.
