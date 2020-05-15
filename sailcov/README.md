sailcov
=======

sailcov is a simple branch coverage visualiser for sail specifications.

### Usage

First, compile your model to c using the `-c_coverage` flag and
including the [sail_coverage.h](../lib/sail_coverage.h) header via
the `-c_include sail_coverage.h` flag. Currently the `-c_coverage`
option will print information about possible branches and function
calls to stdout, which will be needed later, so redirect this to a
file called `all_branches`, i.e.

```
sail -c -c_coverage -c_include sail_coverage.h my_model.sail -o my_model > all_branches
```

Next we need to link implementations of the coverage tracking
functions into the generated C. This done by using the static library
in [lib/coverage/](../lib/coverage/). Currently this is written in Rust
for want of an obvious hashset implementation in C and can be built
using `cargo build --release` which will produce a `libsail_coverage.a`
static library. Once this is done, we can link this into our C
emulator by passing `$SAIL_DIR/lib/coverage/libsail_coverage.a
-lpthread -ldl` to gcc, where SAIL_DIR is the location of this
repository.

Finally, when we run our model it will append coverage information
into a file called `sail_coverage`. The tool in this directory can
compare that with the data contained in the `all_branches` file
described above and produce an html coverage report for each file in
the specification. For example:

```
sailcov -a all_branches -t sail_coverage my_model.sail
```

which produces a `my_model.html` file. Multiple sail files can be
passed to the tool, and it will produce html for each
individually. See
[riscv_vmem_sv39.html](https://alasdair.github.io/riscv_vmem_sv39.html)
for an example of the output. There is also a `--tab-width` option for
sailcov that can be used to control the tab width in the generated
html.

### Colour options

`sailcov -h` will list the available options for the colours used in
the output. The hue and saturation for the colours used for covered
and uncovered code can be individually set. Or the default red/green
colours for uncovered/covered can be swapped for a yellow/blue theme
using `--alt-colors` or `--alt-colours`. See the alternate
[riscv_vmem_sv39.html](https://alasdair.github.io/riscv_vmem_sv39_alt.html)
for an example.
