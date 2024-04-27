![Sail logo](https://github.com/rems-project/sail/blob/sail2/etc/logo/sail_logo.png?raw=true)

The Sail ISA specification language
===================================

[![Build and Test](https://github.com/rems-project/sail/actions/workflows/build.yml/badge.svg)](https://github.com/rems-project/sail/actions/workflows/build.yml)

Overview
--------

Sail is a language for defining the instruction-set architecture
(ISA) semantics of processors: the architectural specification of the behaviour of machine instructions.
Sail is an engineer-friendly language, much like earlier vendor pseudocode, 
but more precisely defined and with tooling to support a wide range of use-cases.
Given a Sail ISA specification, the tool can:

- type-check it, to check e.g. that there are no unintended mismatches of bitvector lengths
- generate documentation snippets, using either LaTeX or AsciiDoc, that can be included directly in ISA documents
(see e.g. the [CHERI ISAv9](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-987.pdf#page=176) spec from p176 for CHERI RISC-V, the [CHERIoT](https://www.microsoft.com/en-us/research/uploads/prod/2023/02/cheriot-63e11a4f1e629.pdf#page=91) spec from p91, and the [Sail AsciiDoctor documentation for RISC-V](https://github.com/Alasdair/asciidoctor-sail/blob/master/doc/built/sail_to_asciidoc.pdf))
- generate executable emulators, in C or OCaml, that can be used as an authoritative reference in sequential-code testing and for early software bring-up
- show specification coverage, of tests running in that generated C emulator
- generate versions of the ISA in the form needed by relaxed memory model tools, 
[isla-axiomatic](https://github.com/rems-project/isla)
and 
[RMEM](http://www.cl.cam.ac.uk/users/pes20/rmem), to compute the allowed behaviour of concurrent litmus tests with respect to architectural relaxed memory models, as an authoritative reference for the concurrency behaviour
- support automated instruction-sequence test generation from the specification in ways that get good specification coverage, using the [Isla](https://github.com/rems-project/isla) SMT-based symbolic evaluation engine for Sail
- generate theorem-prover-definition versions of the ISA specification, in Coq, Isabelle, or HOL4, that support interactive proof in those systems, e.g. that the ISA satisfies intended security properties, such as our [proofs for the Arm Morello ISA](http://www.cl.cam.ac.uk/~pes20/morello-proofs-esop2022.pdf)
- (in progress) generate a reference ISA model in SystemVerilog, that can be used as a reference for hardware verification (e.g. using JasperGold)
- support interactive proof about sequential binary code, integrating the Isla symbolic evaluator and the Iris program logic in [Islaris](https://github.com/rems-project/islaris).

(Not all of these are currently supported for all models - check the current status as needed.)

![Sail overview](https://github.com/rems-project/sail/blob/sail2/etc/overview/overview-sail.png?raw=true)


The language is essentially a first-order imperative language, but
with lightweight dependent typing for numeric types and bitvector
lengths, which are automatically checked using the Z3 SMT solver.


Sail ISA Models
---------------

Sail has been used for Arm-A, Morello (CHERI-Arm), RISC-V, CHERI-RISC-V, CHERIoT, x86, CHERI x86, MIPS, CHERI-MIPS, and IBM Power.  In most cases these are full definitions (e.g. able to boot an OS in the Sail-generated emulator), but x86, CHERI x86 and IBM Power are core user-mode fragments, and the last is in an older legacy version of Sail. 

* [Sail Arm-A (from ASL)](https://github.com/rems-project/sail-arm).
These are complete ISA models for Armv9.4-A, Armv9.3-A, and Armv8.5-A,  automatically generated from the Arm-internal ASL reference (as used in the Arm reference manual). They are provided under a BSD 3-Clause Clear license, by agreement with Arm. 
The older  [Sail Armv8.3-A](https://github.com/rems-project/sail/tree/sail2/aarch64)
model, the "public" model described in our [POPL 2019 paper](http://www.cl.cam.ac.uk/users/pes20/sail/sail-popl2019.pdf), is still available but is largely superseded. 
There is also an older  [handwritten Sail Armv8-A ISA model](https://github.com/rems-project/sail/tree/sail2/aarch64_small)
     for a user-mode fragment.

* [Sail Morello (CHERI-Arm) ISA model (from ASL)](https://github.com/CTSRD-CHERI/sail-morello), for the Arm Morello CHERI-enabled prototype architecture. This is similarly  automatically generated from the complete Arm-internal ASL definition.  This was the basis for our [Morello security proofs](https://github.com/CTSRD-CHERI/sail-morello-proofs/blob/public/README.md).

* [Sail RISC-V ISA model](https://github.com/riscv/sail-riscv). This has been adopted by the RISC-V Foundation.

* [Sail CHERI RISC-V model](https://github.com/CTSRD-CHERI/sail-cheri-riscv). This is the specification of the CHERI extensions to RISC-V, developed in the [CHERI](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/) project. 

* [Sail CHERIoT](https://github.com/microsoft/cheriot-sail). This is the Microsoft specification of their [CHERIoT](https://www.microsoft.com/en-us/research/publication/cheriot-rethinking-security-for-low-cost-embedded-systems/)  ISA design for small embedded cores with CHERI protection. 

* [Sail x86 (from ACL2)](https://github.com/rems-project/sail-x86-from-acl2). This is a version of the 
[X86isa](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/ACL2____X86ISA) formal model of a substantial part of the x86 ISA in ACL2, by Shilpi Goel, Warren A. Hunt, Jr., and Matt Kaufmann, automatically translated into Sail.

* [Sail MIPS and CHERI-MIPS ISA models, handwritten](https://github.com/CTSRD-CHERI/sail-cheri-mips). These are specifications of MIPS and CHERI MIPS developed in the first realisation of the CHERI architecture extensions in the [CHERI](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/) project.

* [Sail IBM POWER ISA model (from IBM XML)](https://github.com/rems-project/sail/tree/sail2/old/power).  This is a specification for a user-mode fragment of the IBM Power ISA, semi-automatically translated from their documentation; it is currently in a legacy version of Sail.

* [Sail x86 ISA model (legacy)](https://github.com/rems-project/sail/tree/sail2/old/x86). This is a handwritten user-mode fragment of x86, also in a legacy version of Sail. 

<!--

* [Sail 32-bit RISC-V model, partially handwritten and partially generated](https://github.com/thoughtpolice/rv32-sail). This currently implements a fragment of the machine mode (-M) specification for RV32IM. (Developed independently of the full RISC-V model for the REMS project.)

-->



Example
-------

For example, below are excerpts from the Sail RISC-V specification defining the "ITYPE" instructions, for addition, subtraction, etc. 
First there is the assembly abstract syntax tree (AST) clause for the ITYPE instructions:
```
union clause ast = ITYPE : (bits(12), regbits, regbits, iop)
```
then the definition of the encode/decode functions between 32-bit opcodes and the AST for these instructions:
```
mapping clause encdec = ITYPE(imm, rs1, rd, op) <-> imm @ rs1 @ encdec_iop(op) @ rd @ 0b0010011
```
and finally the execution semantics for the ITYPE instructions:
```
function clause execute (ITYPE (imm, rs1, rd, op)) = {
  let rs1_val = X(rs1);                      // read the source register rs1
  let immext : xlenbits = EXTS(imm);         // sign-extend the immediate argument imm
  let result : xlenbits = match op {         // compute the result
    RISCV_ADDI  => rs1_val + immext,         // ...for ADDI, do a bitvector addition
    RISCV_SLTI  => EXTZ(rs1_val <_s immext),
    RISCV_SLTIU => EXTZ(rs1_val <_u immext),
    RISCV_ANDI  => rs1_val & immext,
    RISCV_ORI   => rs1_val | immext,
    RISCV_XORI  => rs1_val ^ immext
  };
  X(rd) = result;                            // write the result to the destination register
  true                                       // successful termination
}
```


This repository
----------------

This repository contains the implementation of Sail, together with
some Sail specifications and related tools.

* A manual, [doc/manual.html](doc/manual.html) with source (in [doc/](doc/)), currently [available online here](https://alasdair.github.io/manual.html)

* The Sail source code (in [src/](src/))

* Generated Isabelle snapshots of some ISA models, in [snapshots/isabelle](snapshots/isabelle)

* Documentation for generating Isabelle and working with the ISA specs
  in Isabelle in [lib/isabelle/manual.pdf](lib/isabelle/manual.pdf)

* Simple emacs and VSCode modes with syntax highlighting (in [editors/](editors/))

* A test suite for Sail (in [test/](test/))

The support library for Coq models is in [a separate repository](https://github.com/rems-project/coq-sail) to help our package management.


Installation
------------

See [INSTALL.md](INSTALL.md) for how
to install Sail using opam.


Editor support
--------------

**Emacs Mode**
[editors/sail-mode.el](editors/sail-mode.el) contains an Emacs mode
for the most recent version of Sail which provides some basic syntax
highlighting.

**VSCode Mode**
[editors/vscode](editors/vscode) contains a Visual Studio Code mode
which provides some basic syntax highlighting. It is also available
on the VSCode Marketplace.

**CLion/PyCharm Syntax highlighting**
[editors/vscode/sail](editors/vscode/sail) contains a Visual Studio Code
mode which provides some basic syntax highlighting. CLion/PyCharm can also
parse the [editors/vscode/sail/syntax/sail.tmLanguage.json](sail.tmLanguage.json)
file and use it to provide basic syntax highlighting.
To install open `Preferences > Editor > TextMate Bundles`. On that settings
page press the `+` icon and locate the [editors/vscode/sail](editors/vscode/sail)
directory.
This requires the [TextMate Bundles plugin](https://plugins.jetbrains.com/plugin/7221-textmate-bundles).

**Vim**
[editors/vim](editors/vim) contains support for syntax highlighting in the vim
editor, in vim's usual format of an `ftdetect` directory to detect Sail files
and a `syntax` directory to provide the actual syntax highlighting.<

Logo
----

[etc/logo](etc/logo) contains the Sail logo (thanks to Jean Pichon, [CC0](https://creativecommons.org/publicdomain/zero/1.0/))
)

Licensing
----------

The Sail implementation, in src/, as well as its tests in test/ and
other supporting files in lib/ and language/, is distributed under the
2-clause BSD licence in the headers of those files and in src/LICENCE.

The generated parts of the ASL-derived Arm-A and Morello models are
copyright Arm Ltd, and distributed under a BSD Clear licence. See https://github.com/meriac/archex, and the
[README file](aarch64/README) in that directory.

The hand-written Armv8 model, in arm/, is distributed under the
2-clause BSD licence in the headers of those files.

The x86 model in x86/ is distributed under the 2-clause BSD licence in
the headers of those files.

The POWER model in power/ is distributed under the 2-clause BSD licence in
the headers of those files.

The models in separate repositories are licensed as described in each. 


People
------

Sail itself is developed by

- [Alasdair Armstrong    ](http://alasdair.io/                     )  (University of Cambridge) - the main developer
- [Thomas Bauereiss      ](http://www.cl.cam.ac.uk/~tb592          )  (University of Cambridge)
- [Brian Campbell        ](http://homepages.inf.ed.ac.uk/bcampbe2/ )  (University of Edinburgh)
- [Shaked Flur           ](http://www.cl.cam.ac.uk/~sf502          )  (~~University of Cambridge~~ Google)
- [Neel Krishnaswami     ](http://www.cl.cam.ac.uk/~nk480/         )  (University of Cambridge)
- [Christopher Pulte     ](http://www.cl.cam.ac.uk/~cp526/         )  (University of Cambridge)
- [Alastair Reid         ](https://alastairreid.github.io/         )  (~~ARM~~Intel)
- [Peter Sewell          ](http://www.cl.cam.ac.uk/~pes20          )  (University of Cambridge)
- [Ian Stark             ](http://homepages.inf.ed.ac.uk/stark/    )  (University of Edinburgh)
 
and previously:

- [Jon French            ](http://www.cl.cam.ac.uk/~jf451/         )  (University of Cambridge)
- [Kathryn E. Gray       ](http://www.cl.cam.ac.uk/~keg29/         )  (~~University of Cambridge~~ Meta)
- [Gabriel Kerneis       ](http://gabriel.kerneis.info/            )  (~~University of Cambridge~~ Google)
- [Prashanth     Mundkur ](http://www.csl.sri.com/people/mundkur/  )  (SRI International)
- [Robert Norton-Wright  ](http://www.cl.cam.ac.uk/~rmn30/         )  (~~University of Cambridge~~ Microsoft)
- [Mark Wassell          ](http://www.cl.cam.ac.uk/~mpew2          )  (University of Cambridge)

Many others have worked on specific Sail models, including in the [CHERI](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/) team, in the RISC-V community, and in the 
[CHERIoT](https://www.microsoft.com/en-us/research/publication/cheriot-rethinking-security-for-low-cost-embedded-systems/) team.



Papers
------

The best starting point is the [POPL 2019 paper](http://www.cl.cam.ac.uk/users/pes20/sail/sail-popl2019.pdf).

<ul>

<li>
<a name="acs-2020"></a>
<a href="https://www.cl.cam.ac.uk/~pes20/slides-acs-2022.pdf">Multicore Semantics: Making Sense of Relaxed Memory (MPhil
  slides)</a>, Peter Sewell, Christopher Pulte, Shaked Flur, Mark
  Batty, Luc Maranget, and Alasdair Armstrong, October 2022.
[&nbsp;<a href="topic.ISA_semantics_bib.html#acs-2020">bib</a>&nbsp;| 
<a href="https://www.cl.cam.ac.uk/~pes20/slides-acs-2022.pdf">.pdf</a>&nbsp;]
</li>


<li>
<a name="2022-pldi-islaris"></a>
<a href="http://www.cl.cam.ac.uk/~pes20/2022-pldi-islaris.pdf">Islaris: Verification of Machine Code Against Authoritative
  ISA Semantics</a>.
 Michael Sammler, Angus Hammond, Rodolphe Lepigre, Brian Campbell,
  Jean Pichon-Pharabod, Derek Dreyer, Deepak Garg, and Peter Sewell.
 In PLDI 2022.
[&nbsp;<a href="topic.ISA_semantics_bib.html#2022-pldi-islaris">bib</a>&nbsp;| 
<a href="http://dx.doi.org/10.1145/3519939.3523434">doi</a>&nbsp;| 
<a href="https://github.com/rems-project/islaris">project page</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/2022-pldi-islaris.pdf">pdf</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#2022-pldi-islaris">abstract</a>&nbsp;]
</li>


<li>
<a name="morello-proofs-esop2022"></a>
<a href="http://www.cl.cam.ac.uk/~pes20/morello-proofs-esop2022.pdf">Verified Security for the Morello Capability-enhanced
  Prototype Arm Architecture</a>.
 Thomas Bauereiss, Brian Campbell, Thomas Sewell, Alasdair Armstrong,
  Lawrence Esswood, Ian Stark, Graeme Barnes, Robert N.&nbsp;M. Watson, and Peter
  Sewell.
 In ESOP 2022.
[&nbsp;<a href="topic.ISA_semantics_bib.html#morello-proofs-esop2022">bib</a>&nbsp;| 
<a href="http://dx.doi.org/10.1007/978-3-030-99336-8\_7">doi</a>&nbsp;| 
<a href="https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/">project page</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/morello-proofs-esop2022.pdf">pdf</a>&nbsp;| 
<a href="https://doi.org/10.1007/978-3-030-99336-8\_7">http</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#morello-proofs-esop2022">abstract</a>&nbsp;]
</li>


<li>
<a name="isla-cav"></a>
<a href="https://www.cl.cam.ac.uk/~pes20/isla/isla-cav2021-extended.pdf">Isla: Integrating full-scale ISA semantics and axiomatic
  concurrency models</a>.
 Alasdair Armstrong, Brian Campbell, Ben Simner, Christopher Pulte,
  and Peter Sewell.
 In CAV 2021.
[&nbsp;<a href="topic.ISA_semantics_bib.html#isla-cav">bib</a>&nbsp;| 
<a href="http://dx.doi.org/10.1007/978-3-030-81685-8\_14">doi</a>&nbsp;| 
<a href="https://www.cl.cam.ac.uk/~pes20/isla/isla-cav2021-extended.pdf">pdf</a>&nbsp;| 
<a href="https://doi.org/10.1007/978-3-030-81685-8\_14">http</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#isla-cav">abstract</a>&nbsp;]
</li>


<li>
<a name="sail-popl2019"></a>
<a href="http://www.cl.cam.ac.uk/users/pes20/sail/sail-popl2019.pdf">ISA Semantics for ARMv8-A, RISC-V, and
  CHERI-MIPS</a>.
 Alasdair Armstrong, Thomas Bauereiss, Brian Campbell, Alastair Reid,
  Kathryn&nbsp;E. Gray, Robert&nbsp;M. Norton, Prashanth Mundkur, Mark Wassell, Jon
  French, Christopher Pulte, Shaked Flur, Ian Stark, Neel Krishnaswami, and
  Peter Sewell.
 In POPL 2019, Proc. ACM Program. Lang. 3, POPL, Article 71.
[&nbsp;<a href="topic.ISA_semantics_bib.html#sail-popl2019">bib</a>&nbsp;| 
<a href="http://dx.doi.org/10.1145/3290384">doi</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/users/pes20/sail/popl2019.html">supplementary material</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/sail/">project page</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/users/pes20/sail/sail-popl2019.pdf">pdf</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#sail-popl2019">abstract</a>&nbsp;]
</li>


<li>
<a name="sail-arw18-minisail"></a>
<a href="http://www.cl.cam.ac.uk/~pes20/sail/arw18_mpew2.pdf">Formalisation of MiniSail in the Isabelle Theorem
  Prover</a>.
 Alasdair Armstrong, Neel Krishnaswami, Peter Sewell, and Mark
  Wassell.
 In Automated Reasoning Workshop (ARW) 2018, Two-page abstract.
[&nbsp;<a href="topic.ISA_semantics_bib.html#sail-arw18-minisail">bib</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/sail/">project page</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/sail/arw18_mpew2.pdf">pdf</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#sail-arw18-minisail">abstract</a>&nbsp;]
</li>


<li>
<a name="sail-arw18"></a>
<a href="http://www.cl.cam.ac.uk/~pes20/sail/2018-04-12-arw-paper.pdf">Detailed Models of Instruction Set Architectures: From
  Pseudocode to Formal Semantics</a>.
 Alasdair Armstrong, Thomas Bauereiss, Brian Campbell, Shaked Flur,
  Kathryn&nbsp;E. Gray, Prashanth Mundkur, Robert&nbsp;M. Norton, Christopher Pulte,
  Alastair Reid, Peter Sewell, Ian Stark, and Mark Wassell.
 In Automated Reasoning Workshop (ARW) 2018, Two-page abstract.
[&nbsp;<a href="topic.ISA_semantics_bib.html#sail-arw18">bib</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/sail/">project page</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/sail/2018-04-12-arw-paper.pdf">pdf</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#sail-arw18">abstract</a>&nbsp;]
</li>


<li>
<a name="armv8-mca"></a>
<a href="http://www.cl.cam.ac.uk/~pes20/armv8-mca/armv8-mca-draft.pdf">Simplifying ARM Concurrency: Multicopy-atomic Axiomatic and
  Operational Models for ARMv8</a>.
 Christopher Pulte, Shaked Flur, Will Deacon, Jon French, Susmit
  Sarkar, and Peter Sewell.
 In POPL 2018.
[&nbsp;<a href="topic.ISA_semantics_bib.html#armv8-mca">bib</a>&nbsp;| 
<a href="http://dx.doi.org/10.1145/3158107">doi</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/armv8-mca/">project page</a>&nbsp;| 
<a href="https://www.cl.cam.ac.uk/~pes20/armv8-mca/errata.html">errata</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/armv8-mca/armv8-mca-draft.pdf">pdf</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#armv8-mca">abstract</a>&nbsp;]
</li>


<li>
<a name="mixed17"></a>
<a href="http://www.cl.cam.ac.uk/~pes20/popl17/mixed-size.pdf">Mixed-size Concurrency: ARM, POWER, C/C++11, and
  SC</a>.
 Shaked Flur, Susmit Sarkar, Christopher Pulte, Kyndylan Nienhuis, Luc
  Maranget, Kathryn&nbsp;E. Gray, Ali Sezgin, Mark Batty, and Peter Sewell.
 In POPL 2017.
[&nbsp;<a href="topic.ISA_semantics_bib.html#mixed17">bib</a>&nbsp;| 
<a href="http://dx.doi.org/10.1145/3009837.3009839">doi</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/users/pes20/popl17/">project page</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/popl17/mixed-size.pdf">pdf</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#mixed17">abstract</a>&nbsp;]
</li>


<li>
<a name="DBLP:conf/popl/FlurGPSSMDS16"></a>
<a href="http://www.cl.cam.ac.uk/~pes20/popl16-armv8/top.pdf">Modelling the ARMv8 architecture, operationally: concurrency
  and ISA</a>.
 Shaked Flur, Kathryn&nbsp;E. Gray, Christopher Pulte, Susmit Sarkar, Ali
  Sezgin, Luc Maranget, Will Deacon, and Peter Sewell.
 In POPL 2016.
[&nbsp;<a href="topic.ISA_semantics_bib.html#DBLP:conf/popl/FlurGPSSMDS16">bib</a>&nbsp;| 
<a href="http://dx.doi.org/10.1145/2837614.2837615">doi</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~sf502/popl16/index.html">project page</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/popl16-armv8/top.pdf">pdf</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#DBLP:conf/popl/FlurGPSSMDS16">abstract</a>&nbsp;]
</li>


<li>
<a name="DBLP:conf/micro/GrayKMPSS15"></a>
<a href="http://www.cl.cam.ac.uk/~pes20/micro-48-2015.pdf">An integrated concurrency and core-ISA architectural envelope
  definition, and test oracle, for IBM POWER multiprocessors</a>
  .
 Kathryn&nbsp;E. Gray, Gabriel Kerneis, Dominic&nbsp;P. Mulligan, Christopher
  Pulte, Susmit Sarkar, and Peter Sewell.
 In MICRO 2015.
[&nbsp;<a href="topic.ISA_semantics_bib.html#DBLP:conf/micro/GrayKMPSS15">bib</a>&nbsp;| 
<a href="http://dx.doi.org/10.1145/2830772.2830775">doi</a>&nbsp;| 
<a href="http://www.cl.cam.ac.uk/~pes20/micro-48-2015.pdf">pdf</a>&nbsp;| 
<a href="topic.ISA_semantics_abstracts.html#DBLP:conf/micro/GrayKMPSS15">abstract</a>&nbsp;]
</li>

</ul>

Funding 
-------

This work was partially supported by the UK Government Industrial Strategy Challenge Fund (ISCF) under the Digital Security by Design (DSbD) Programme, to deliver a DSbDtech enabled digital platform (grant 105694).
This project has received funding from the European Research Council
(ERC) under the European Union's Horizon 2020 research and innovation programme (grant agreement No 789108, ELVER).
This work was partially supported by EPSRC grant EP/K008528/1 <a href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous Engineering for
  Mainstream Systems</a>,
an ARM iCASE award, and EPSRC IAA KTF funding.
This work was partially supported by donations from Arm and Google.
The Sail AsciiDoc backend was supported by RISC-V International.
Approved for public release; distribution is unlimited. This research
is sponsored by the Defense Advanced Research Projects Agency (DARPA)
and the Air Force Research Laboratory (AFRL), under contracts
FA8750-10-C-0237 ("CTSRD") and FA8650-18-C-7809 ("CIFV"). The views,
opinions, and/or findings contained in these articles OR presentations are
those of the author(s)/presenter(s) and should not be interpreted as
representing the official views or policies of the Department of
Defense or the U.S. Government.



