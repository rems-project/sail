# Sail RISC-V model for Coq

This directory contains the Coq files for the Sail RISC-V model, in
`sail/riscv`, along with the Sail Coq library (`sail/lib/coq`) and the
MIT BBV library for bitvector support.  The `build` script checks all
of the files, and `clean` removes the generated files.  The main model
is in `sail/riscv/riscv.v`.

The Coq version of the model was generated from the Sail sources
available at <https://github.com/rems-project/sail/tree/sail2/riscv>,
commit `9e9506a582763f7ad4c6c8c57dc514d9fb89b9df`, and were manually
patched to deal with parts of the model that the tool does not fully
deal with, mostly due to recursive functions.  The manual changes can
be found in `sail/riscv/coq.patch`.
