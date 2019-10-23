## Introduction

This directory contains:
* Ott definitions for MiniSail and MiniSail+ (./ott)

To be added:
* ./thy - Isabelle theory files.
* ./src - Code for MiniSail+ backend for Sail.

## MiniSail

MiniSail is a core calculus for Sail that uses refinement types
These are types of the form ```{ z : b | c }``` where v is a variable bound
in the type, b is a base type (such as bool or int) and c is some constraint.
The constraint logic is picked so that satisfiability of constraints can
be checked using an SMT solver such as Z3.

The Ott file, minisail_anf.ott, describes the syntax and type system for MiniSail whilst
in thy/MiniSail is a mechanisation of MiniSail using Nominal2 Isabelle with proofs
of type safety.

## MiniSail+

MiniSail+ is a larger subset of Sail that is able to, at least syntactically,
handle, after conversion from Sail, the Sail RISCV model.

The Ott files, minisailplus_ast_vct.ott, minisailplus_ast_ped.ott and
minisailplus_rules.ott describe the syntax and type system for MiniSail+.

The sail branch 'minisail' (https://github.com/rems-project/sail/tree/minisail)
containts an experimental implementation of Sail to MiniSail+ converter and MiniSail+
type checker as a pass in Sail.

## Converting from Sail to MiniSail+

Conversion of expressions from Sail to MiniSail+ is mostly a direct syntactic
mapping. It can handle the Sail-RISCV model apart from:
* Definition of mapping functions.
* Ref and deref constructs.

Conversion of types however is more involved:
Sail uses its own syntax for its style of refinement types while MiniSail+ uses
the more common form that appears in the literature.

For example, the Sail function type:
```
forall 'n 'm. (int('n+1) , int('m)) -> bool('n == 'm)
```
is converted into the MiniSail type:
```
x : (int,int) -> { z : bool | z = ((fst x - 1) = snd x) }
```
The Sail type has the type level variables ```'n``` and ```'m``` while MiniSail+ uses
the value variables ```x``` and ```z```. To convert the type, an inversion operation occurs
that uses the input type to obtain equations for ```'n``` and ```'m```:

We start with the system of equations:
```
fst x = 'n + 1
snd x = 'm
```
solve for 'n and 'm to obtain

```
'n = fst x - 1
'm = snd x
```

that are then substituted into the return type.
A form of symbolic Gaussian elimination is used to do the inversion.

## MiniSail+ type system
The MiniSail+ type system is described in the Ott file ```minisailplus_rules.ott'''.
It is *indirectly* implemented in the Sail pass described above and the latter can type check
the Sail prelude, but not the Sail-RISCV model.
