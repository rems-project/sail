The Sail ISA specification language
===================================

Overview
========

Sail is a language for describing the instruction semantics of
processors. Sail aims to provide a engineer-friendly,
vendor-pseudocode-like language for describing instruction
semantics. It is an imperative language containing some advanced
features like dependent typing for numeric types and bitvector
lengths, which are automatically checked using Z3. It has been used
for several papers, available from http://www.cl.cam.ac.uk/~pes20/sail/

This repository contains the implementation of Sail, together with
some Sail specifications and related tools.

* A manual, [manual.pdf](manual.pdf) with source (in [doc/](doc/))

* The Sail source code (in [src/](src/))

* A Sail specification of ARMv8.3-A generated from ARM's publically
  released ASL specification (in [aarch64/](aarch64/))

* Generated Isabelle snapshots of the above ISAs in [snapshots/isabelle](snapshots/isabelle)

* Documentation for generating Isabelle and working with the ISA specs
  in Isabelle in [snapshots/isabelle/Manual.pdf](snapshots/isabelle/Manual.pdf)

* A simple emacs mode with syntax highlighting (in [editors/](editors/))

* A test suite for Sail (in [test/](test/))

We also have versions of IBM POWER, a fragment of x86, and a
hand-written fragment of ARMv8-A, but these are currently not up-to-date
with the latest version of Sail, which is the (default) sail2 branch
on Github.

The mips and cheri-mips specifications that used to be here have moved to
https://github.com/CTSRD-CHERI/sail-cheri-mips .

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

[editors/sail2-mode.el](editors/sail2-mode.el) contains an Emacs mode
for the most recent version of Sail which provides some basic syntax
highlighting. [editors/sail-mode.el](editors/sail-mode.el) contains an
emacs mode for previous versions of the language.

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
