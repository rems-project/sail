The Sail ISA specification language
===================================

Overview
========

Sail is a language for describing the instruction-set architecture
(ISA) semantics of processors. Sail aims to provide a
engineer-friendly, vendor-pseudocode-like language for describing
instruction semantics. It is essentially a first-order imperative
language, but with lightweight dependent typing for numeric types and
bitvector lengths, which are automatically checked using Z3. It has
been used for several papers, available from
<http://www.cl.cam.ac.uk/~pes20/sail/>.
<p>

Given a Sail definition, the tool will type-check it and generate
executable emulators, in C and OCaml, theorem-prover definitions for
Isabelle, HOL4, and Coq, and definitions to integrate with our 
<a href="http://www.cl.cam.ac.uk/users/pes20/rmem">RMEM</a> tool for
concurrency semantics.  This is all work in progress, and some
theorem-prover definitions do not yet work for the more complex
models; see the most recent papers and the ARMv8.5-A model for
descriptions of the current state.
<p>

  <img src="https://www.cl.cam.ac.uk/~pes20/sail/overview-sail.png">
<p>

This repository contains the implementation of Sail, together with
some Sail specifications and related tools.

* A manual, [manual.pdf](manual.pdf) with source (in [doc/](doc/))

* The Sail source code (in [src/](src/))

* Generated Isabelle snapshots of some ISA models, in [snapshots/isabelle](snapshots/isabelle)

* Documentation for generating Isabelle and working with the ISA specs
  in Isabelle in [snapshots/isabelle/Manual.pdf](snapshots/isabelle/Manual.pdf)

* A simple emacs mode with syntax highlighting (in [editors/](editors/))

* A test suite for Sail (in [test/](test/))

Sail ISA Models
===============

Sail is currently being used for ARM, RISC-V, MIPS, CHERI-MIPS, IBM Power, and x86 models,  variously ranging from full definitions to core user-mode fragments, and either here or in separate repositories:

### REMS Models

* [Sail ARMv8.5-A ISA model, automatically generated from the ARM-internal ASL reference, as used in the ARM ARM](https://github.com/rems-project/sail-arm).

* [Sail ARMv8.3-A ISA model](https://github.com/rems-project/sail/tree/sail2/arm). This is the "public" model described in our [POPL 2019 paper](http://www.cl.cam.ac.uk/users/pes20/sail/sail-popl2019.pdf), now largely superseded by the above.

* [Sail ARMv8-A ISA model, handwritten](https://github.com/rems-project/sail/tree/sail2/arm). This is a handwritten user-mode fragment.

* [Sail RISC-V ISA model, handwritten](https://github.com/rems-project/sail-riscv). 

* [Sail MIPS and CHERI-MIPS ISA models, handwritten](https://github.com/CTSRD-CHERI/sail-cheri-mips).

* [Sail IBM POWER ISA model, automatically generated from IBM XML documentation](https://github.com/rems-project/sail/tree/sail2/power).  This is a user-mode fragment. 

* [Sail x86 ISA model, handwritten](https://github.com/rems-project/sail/tree/sail2/x86). This is a handwritten user-mode fragment. 

The hand-written ARMv8-A, IBM POWER, and x86 models are currently not in sync
with the latest version of Sail, which is the (default) sail2 branch
on Github.  These and the RISC-V model are integrated with our [RMEM](http://www.cl.cam.ac.uk/users/pes20/rmem) tool for concurrency semantics. 

### External Models

* [Sail 32-bit RISC-V model, partially handwritten and partially generated](https://github.com/thoughtpolice/rv32-sail). This currently implements a fragment of the machine mode (-M) specification for RV32IM. (Developed independently of the full RISC-V model for the REMS project.)

OPAM Installation
=================

See the following Sail [wiki
page](https://github.com/rems-project/sail/wiki/OPAMInstall) for how
to get pre-built binaries of Sail using OPAM.

Building
========

See [INSTALL.md](INSTALL.md) for full details of how to build Sail from source
with all the required dependencies.

Emacs Mode
==========

[editors/sail-mode.el](editors/sail-mode.el) contains an Emacs mode
for the most recent version of Sail which provides some basic syntax
highlighting.

Licensing
=========

The Sail implementation, in src/, as well as its tests in test/ and
other supporting files in lib/ and language/, is distributed under the
2-clause BSD licence in the headers of those files and in src/LICENCE,
with the exception of the library src/pprint, which is distributed
under the CeCILL-C free software licence in src/pprint/LICENSE.

The generated parts of the ASL-derived ARMv8.3 model in aarch64/ are
copyright ARM Ltd. See https://github.com/meriac/archex, and the
[README file](aarch64/README) in that directory.

The hand-written ARMv8 model, in arm/, is distributed under the
2-clause BSD licence in the headers of those files.

The x86 model in x86/ is distributed under the 2-clause BSD licence in
the headers of those files.

The POWER model in power/ is distributed under the 2-clause BSD licence in
the headers of those files.

The models in separate repositories are licensed as described in each. 
