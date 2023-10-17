![Sail logo](https://github.com/rems-project/sail/blob/sail2/etc/logo/sail_logo.png?raw=true)

The Sail ISA specification language
===================================

[![Build and Test](https://github.com/rems-project/sail/actions/workflows/build.yml/badge.svg)](https://github.com/rems-project/sail/actions/workflows/build.yml)

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
documentation, executable emulators (in C and OCaml), theorem-prover definitions (for
Isabelle, HOL4, and Coq), and definitions to integrate with our 
<a href="http://www.cl.cam.ac.uk/users/pes20/rmem">RMEM</a>
and
<a href="https://github.com/rems-project/isla">isla-axiomatic</a>
tools for
concurrency semantics.
The <a href="https://github.com/rems-project/isla">Isla</a> engine provides SMT-based symbolic evaluation for Sail models,
and the <a href="https://github.com/rems-project/islaris">Islaris</a> verification tool integrates Isla output with the Iris program logic to support proof about binary code in Coq. 
Not all models are integrated with all tools - see the most recent papers and models for
descriptions of the current state.
<p>

  <img width="800" src="https://www.cl.cam.ac.uk/~pes20/sail/overview-sail.png?">
<p>

This repository contains the implementation of Sail, together with
some Sail specifications and related tools.

* A manual, [manual.pdf](manual.pdf) with source (in [doc/](doc/))

* The Sail source code (in [src/](src/))

* Generated Isabelle snapshots of some ISA models, in [snapshots/isabelle](snapshots/isabelle)

* Documentation for generating Isabelle and working with the ISA specs
  in Isabelle in [lib/isabelle/manual.pdf](lib/isabelle/manual.pdf)

* Simple emacs and VSCode modes with syntax highlighting (in [editors/](editors/))

* A test suite for Sail (in [test/](test/))

The support library for Coq models is in [a separate repository](https://github.com/rems-project/coq-sail) to help our package management.

Sail ISA Models
===============

Sail is currently being used for Arm-A, Morello (CHERI-Arm), RISC-V, CHERI-RISC-V, MIPS, CHERI-MIPS, IBM Power, and x86 models,  variously ranging from full definitions (able to boot an OS in the Sail-generated emulator) to core user-mode fragments:

### REMS Models

* [Sail Armv9.3-A and Armv8.5-A ISA models, automatically generated from the Arm-internal ASL reference, as used in the Arm ARM](https://github.com/rems-project/sail-arm).

* [Sail Armv8.3-A ISA model](https://github.com/rems-project/sail/tree/sail2/aarch64). This is the "public" model described in our [POPL 2019 paper](http://www.cl.cam.ac.uk/users/pes20/sail/sail-popl2019.pdf), now largely superseded by the above.

* [Sail Armv8-A ISA model, handwritten](https://github.com/rems-project/sail/tree/sail2/aarch64_small). This is a handwritten user-mode fragment.

* [Sail Morello (CHERI-Arm) ISA model](https://github.com/CTSRD-CHERI/sail-morello), automatically generated from the Arm-internal ASL definition.  This was the basis for our [Morello security proofs](https://github.com/CTSRD-CHERI/sail-morello-proofs/blob/public/README.md).

* [Sail RISC-V ISA model, handwritten](https://github.com/riscv/sail-riscv). This has been adopted by the RISC-V Foundation.

* [Sail MIPS and CHERI-MIPS ISA models, handwritten](https://github.com/CTSRD-CHERI/sail-cheri-mips).

* [Sail IBM POWER ISA model, automatically generated from IBM XML documentation](https://github.com/rems-project/sail/tree/sail2/old/power).  This is a user-mode fragment. 

* [Sail x86 ISA model, handwritten](https://github.com/rems-project/sail/tree/sail2/old/x86). This is a handwritten user-mode fragment. 

The hand-written IBM POWER, and x86 models are currently not in sync
with the latest version of Sail, which is the (default) sail2 branch
on Github.  These and the RISC-V model are integrated with our [RMEM](http://www.cl.cam.ac.uk/users/pes20/rmem) tool for concurrency semantics. 

### External Models

* [Sail 32-bit RISC-V model, partially handwritten and partially generated](https://github.com/thoughtpolice/rv32-sail). This currently implements a fragment of the machine mode (-M) specification for RV32IM. (Developed independently of the full RISC-V model for the REMS project.)

Installation
============

See [INSTALL.md](INSTALL.md) for how
to install Sail using opam.

Emacs Mode
==========

[editors/sail-mode.el](editors/sail-mode.el) contains an Emacs mode
for the most recent version of Sail which provides some basic syntax
highlighting.

VSCode Mode
===========

[editors/vscode](editors/vscode) contains a Visual Studio Code mode
which provides some basic syntax highlighting. It is also available
on the VSCode Marketplace.

CLion/PyCharm Syntax highlighting
===========

[editors/vscode/sail](editors/vscode/sail) contains a Visual Studio Code
mode which provides some basic syntax highlighting. CLion/PyCharm can also
parse the [editors/vscode/sail/syntax/sail.tmLanguage.json](sail.tmLanguage.json)
file and use it to provide basic syntax highlighting.
To install open `Preferences > Editor > TextMate Bundles`. On that settings
page press the `+` icon and locate the [editors/vscode/sail](editors/vscode/sail)
directory.

This requires the [TextMate Bundles plugin](https://plugins.jetbrains.com/plugin/7221-textmate-bundles).

Vim
===

[editors/vim](editors/vim) contains support for syntax highlighting in the vim
editor, in vim's usual format of an `ftdetect` directory to detect Sail files
and a `syntax` directory to provide the actual syntax highlighting.

Logo
====

[etc/logo](etc/logo) contains the Sail logo

Licensing
=========

The Sail implementation, in src/, as well as its tests in test/ and
other supporting files in lib/ and language/, is distributed under the
2-clause BSD licence in the headers of those files and in src/LICENCE.

The generated parts of the ASL-derived Armv8.5 and Armv8.3 models are
copyright Arm Ltd, and distributed under a BSD Clear licence. See https://github.com/meriac/archex, and the
[README file](aarch64/README) in that directory.

The hand-written Armv8 model, in arm/, is distributed under the
2-clause BSD licence in the headers of those files.

The x86 model in x86/ is distributed under the 2-clause BSD licence in
the headers of those files.

The POWER model in power/ is distributed under the 2-clause BSD licence in
the headers of those files.

The models in separate repositories are licensed as described in each. 

## Funding 

This work was partially supported by the UK Government Industrial Strategy Challenge Fund (ISCF) under the Digital Security by Design (DSbD) Programme, to deliver a DSbDtech enabled digital platform (grant 105694).
This project has received funding from the European Research Council
(ERC) under the European Union’s Horizon 2020 research and innovation programme (grant agreement No 789108, ELVER).
This work was partially supported by EPSRC grant EP/K008528/1 <a href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous Engineering for
  Mainstream Systems</a>,
an ARM iCASE award, and EPSRC IAA KTF funding.
This work was partially supported by donations from Arm and Google.
Approved for public release; distribution is unlimited. This research
is sponsored by the Defense Advanced Research Projects Agency (DARPA)
and the Air Force Research Laboratory (AFRL), under contracts
FA8750-10-C-0237 ("CTSRD") and FA8650-18-C-7809 ("CIFV"). The views,
opinions, and/or findings contained in these articles OR presentations are
those of the author(s)/presenter(s) and should not be interpreted as
representing the official views or policies of the Department of
Defense or the U.S. Government.



