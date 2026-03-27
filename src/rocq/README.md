= Sail Rocq Sources

This directory defines the abstract syntax and semantics of the Sail
language formally in Rocq.

== Extraction

The extraction to OCaml code is handled by [extract/prelude/SailExtraction.v](extract/prelude/SailExtraction.v).

Currently, rather than generating a dune library, we instead copy and
check-in the extracted source directly into the Sail
`src/lib/extraction` directory, where they can be accessed using
`Extraction.Module`. This is accomplished with some Makefile/dune
trickery, using the exhaustive list of extracted modules in
[extract/gen/modules.txt](extract/gen/modules.txt).

The reason we do this is mostly to keep the build process as simple as
possible, and avoid any issues with building Sail natively on Windows.

== Style

Rocq source should follow the [Iris style guide](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/style_guide.md),
with the exception that match bodies should be indented by two spaces and not one.

Tactics should preferably be defined using Ltac2.

In general, Rocq definitions should be set up so they extract cleanly
into OCaml. Practically, this means writing in a simple functional
style, and preferring modules to typeclasses for definitions
(proofs/proof automation can still use typeclasses).
