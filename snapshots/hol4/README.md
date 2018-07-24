# Snapshot of HOL4 output for Sail CHERI and RISC-V models

These theories are a snapshot of the generated files for the Sail
MIPS, CHERI, RISC-V, and Aarch64 models, translated to HOL4 via Lem.
They only require HOL4; the necessary Lem library files are included.

A recent checkout of HOL4 from the repository at
<https://github.com/HOL-Theorem-Prover/HOL/> is required.  This snapshot was
successfully built with commit `7ed3f12`, for example.  Some older versions
will fail with a Holdep error due to a lexer bug in HOL that has now been
fixed.

Note that HOL4 takes a substantial amount of time to process the definition of
the `regstate` record.  In particular, allow over an hour for the MIPS model.
