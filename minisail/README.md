# MiniSail

Formalisation of Sail is by means of two languages:
First, MiniSail-ANF that captures just enough of the key features of Sail to allow us to
prove type saferty.
Second, MiniSail+ that captures almost all of Sail; enough to handle almost all of the Sail RISCV model.

## MiniSail-ANF

MiniSail-ANF is a core calculus for Sail that uses administrative normal form to make
the types of complex terms explicit and thus simplifying the typing rules.
The syntax covers immutable and mutable variables, basic control statements, pattern matching,
functions and refinement types.

Refinement types are types of the form ```{ z : b | c }``` where v is a variable bound
in the type, b is a base type (such as bool or int) and c is some constraint that can mention ```z```
as well as program variables in the current context.
The constraint logic is picked so that satisfiability of constraints can
be checked using an SMT solver such as Z3.

The Ott file, minisail_anf.ott, describes the syntax, the type system
and operational semantics for MiniSail-ANF.
Proofs of type safety have been developed on paper and in Isabelle.

See the POPL 2019 [paper](http://www.cl.cam.ac.uk/users/pes20/sail/sail-popl2019.pdf) for an overview of MiniSail-ANF.


## MiniSail+

MiniSail+ is a larger subset of Sail with a syntax that is more closely aligned to Sail.
The [Sail RISCV model](https://github.com/rems-project/sail-riscv) can be converted (with
a few ommissions) into MiniSail+.
An experimental implementation of a Sail to MiniSail+ converter and a MiniSail+
type checker is available.
Source for this is located in sail_root/src/minisail and makes use of ML code
exported from Isabelle.

### Syntax

The syntax for MiniSail+ expressions closely follows the Sail syntax and conversion from Sail
expressions to MiniSail+ ones is straightforward.
The Sail-RISCV model can be converted into MiniSail+ apart from:
* Definition of mapping functions.
* Deref constructs.

However, for types Sail has its own style of refinement types rather than then more
common form that appears in the literature.
Sail makes use of type level variables in the constraints and these
transfer information about program variables into the constraint.
In MiniSail+ program variables can appear in the constraints directly.

For example, in Sail a function comparing the successor of one integer with another has
the type:
```
forall 'n 'm. (int('n+1) , int('m)) -> bool('n == 'm)
```
in MiniSail+ it has the type:
```
x : (int,int) -> { z : bool | z = ((fst x - 1) = snd x) }
```
The Sail type has the type level variables ```'n``` and ```'m``` while MiniSail+ uses
the value variables ```x``` and ```z```.
The type level variables carry the information about the function arguments into the constraint
refining the functions return value.
To convert the type, an inversion operation occurs
that uses the function's input type to obtain equations for ```'n``` and ```'m```:

We start with the system of equations:
```
fst x = 'n + 1
snd x = 'm
```
solve for 'n and 'm to obtain the equations

```
'n = fst x - 1
'm = snd x
```

that are then substituted into the return type.
A form of symbolic Gaussian elimination is used to do the inversion.

### Type system
The MiniSail+ type system is described in the Ott file ```minisailplus_rules.ott'''.

The typing rules are bidirectional with type checking and type synthesis forms.
Generally, for top level nonterminals (such as definitions), the checking rules are primary,
and for lowest level nonterminals (such as values), the synthesis rules are primary.
The aim is to minimise the amount of type annotations the programmer needs to include in their program.
There are some expression constructs
where this is not possible and so the programmer needs to provide type annotation.
Importantly, expressions with branching, match and if, don't have type synthesis rule.

In MiniSail-ANF we partition expression forms where checking occurs into MiniSail-ANF statements and
expressions where synthesis occurs into MiniSail-ANF expressions. This is not done in MiniSail+
to maintain the closer connection to Sail. 

The following contexts are used in the judgements:
* T - contains type definitions.
* P - contains function definitions.
* G - contains immutable variables.
* D - contains mutable variables.

The judgements are:
* T |- b1 < b2 -  Base type subtyping.
* T ; G |- t1 < t2. Refinement type subtyping.
* T ; G |- v => t. Value type synthesis.
* T ; G |- v <= t. Value type checking.
* T ; G |- pat <= t ~> x ; klist ; xlist. Pattern type checking.
* T ; G |- pat => t ~> x ; klist ; xlist. Pattern type synthesis.
* T ; P : G ; D |- lexp <= t ~> D'. L-value expression type checking. D' is an updated
mutable variable context.
• T ; P ; G ; D |- lexp => t ~> D'. L-value expression type synthesis.
• T ; P ; G ; D |- pexp <= t ~> G'. Pattern-expression type checking.
• T ; P ; G ; D |- (a1 .. an ) e => t ~> x ; klist. Overloaded function type synthesis.
• T ; P ; G ; D |- letbind ~> klist Let-bind type checking.
* T ; P ; G ; D |- e => t ~> x ; klist. Type synthesis judgement for general expressions. klist is
the list of sub-expression variables and their types. We don’t need klist for value type
synthesis as the variables are already at the level of sub-expression variables.
* T ; P ; G ; D |- e <= t. Type checking judgement for expressions.
* Various judgements for checking top-level definitions.


For many of the MiniSail+ expresion forms, the typing rule is obvious or a lifting of the
MiniSail-ANF rule with the addition of information
that tracks typing of subterms of complex terms.
This tracking is handled in the rules
use the klist nonterminal (`little gamma') that contains type information for sub-terms of terms.
Fresh variables are created that represent the values of subterms and have types registered in the
klist.

This type system is implemented in the Sail pass described above and can type check
the Sail prelude, but not the complete Sail-RISCV model.

### MiniSail+ Ott Definitions

This directory contains:
* Ott definitions for MiniSail and MiniSail+ (./ott)
* Coq generated from Ott definitions (./ott/coq_snapshot)

The syntax and type system for MiniSail+ are defined using [Ott](https://www.cl.cam.ac.uk/~pes20/ott) in the following
files:

* minisailplus_ast_vct.ott - Syntax for values, constraints and types.
* minisailplus_ast_ped.ott - Syntax for patterns, expressions and definitions.
* minisailplus_rules.ott - Typing rules.

PDF and Coq theorem prover files can be generated from these files (using the Makefile).
Coq prover files require the Ott Coq support library installed from OPAM.
This can be installed using 'opam install coq-ott'. It has been test-compiled with Coq 8.5 through 8.10.0.

For Coq prover backend, the definition of the necessary homs is complete but
the Coq functions are stubs.

These definitions are part a larger work and so include what might be considered noise
when viewed on their own. For example, the superscripts on the non-terminals in the PDF
are so that we can distinguish between MiniSail and Sail when describing elaboration
(which isn't included here). This case can be handled with `comment-filtering'.

What isn't described, and plays and important role, is the validity judgement |=. This is
the point at which an SMT problem is generated and SMT invoked as part of
subtype checking.
