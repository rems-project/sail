# Snapshot of HOL4 output for Sail CHERI and RISC-V models

These theories are a snapshot of the generated files for the Sail
MIPS, CHERI, RISC-V, and Aarch64 models, translated to HOL4 via Lem.
They only require HOL4; the necessary Lem library files are included.

Note that HOL4 takes a substantial amount of time to process the definition of
the `regstate` record.  In particular, allow over an hour for the MIPS model.
